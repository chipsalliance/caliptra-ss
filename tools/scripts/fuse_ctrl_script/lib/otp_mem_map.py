#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""OTP memory map class, used to create the associated RTL and
documentation, and to create OTP memory images for preloading.
"""
import logging as log
from math import ceil, log2
from pathlib import Path
from typing import Dict, List

from lib.prim_mubi import is_width_valid, mubi_value_as_int
import hjson
from tabulate import tabulate

import lib.secure_prng as sp
from lib.common import check_bool, check_int, random_or_hexvalue

DIGEST_SUFFIX = "_DIGEST"
DIGEST_SIZE = 8

# Seed diversification constant for OtpMemMap (this enables to use
# the same seed for different classes)
OTP_SEED_DIVERSIFIER = 177149201092001677687

# This must match the rtl parameter ScrmblBlockWidth / 8
SCRAMBLE_BLOCK_WIDTH = 8


def _validate_otp(otp: Dict):
    '''Validate OTP entry'''
    otp.setdefault("depth", "1024")
    otp.setdefault("width", "2")
    otp["depth"] = check_int(otp["depth"])
    otp["width"] = check_int(otp["width"])
    otp["size"] = otp["depth"] * otp["width"]
    otp["addr_width"] = ceil(log2(check_int(otp["depth"])))
    otp["byte_addr_width"] = ceil(log2(otp["size"]))


def _validate_scrambling(scr: Dict):
    '''Validate SCrambling entry'''
    scr.setdefault("key_size", "16")
    scr.setdefault("iv_size", "8")
    scr.setdefault("cnst_size", "16")
    scr["key_size"] = check_int(scr["key_size"])
    scr["iv_size"] = check_int(scr["iv_size"])
    scr["cnst_size"] = check_int(scr["cnst_size"])

    if "keys" not in scr:
        raise RuntimeError("Missing key configuration.")
    if "digests" not in scr:
        raise RuntimeError("Missing digest configuration.")

    for key in scr["keys"]:
        key.setdefault("name", "unknown_key_name")
        key.setdefault("value", "<random>")
        random_or_hexvalue(key, "value", scr["key_size"] * 8)

    for dig in scr["digests"]:
        dig.setdefault("name", "unknown_key_name")
        dig.setdefault("iv_value", "<random>")
        dig.setdefault("cnst_value", "<random>")
        random_or_hexvalue(dig, "iv_value", scr["iv_size"] * 8)
        random_or_hexvalue(dig, "cnst_value", scr["cnst_size"] * 8)


# if remaining number of bytes are not perfectly aligned, truncate
def _avail_blocks(size: int) -> int:
    return int(size / SCRAMBLE_BLOCK_WIDTH)


# distribute number of blocks among partitions
def _dist_blocks(num_blocks: int, parts: List):
    num_parts = len(parts)

    if not num_parts:
        return

    # Very slow looping
    for i in range(num_blocks):
        parts[i % num_parts]['size'] += SCRAMBLE_BLOCK_WIDTH


# distribute unused otp bits
def _dist_unused(config: Dict, allocated: int):

    # determine how many aligned blocks are left
    # unaligned bits are not used
    leftover_blocks = _avail_blocks(config['otp']['size'] - allocated)

    # sponge partitions are partitions that will accept leftover allocation
    sponge_parts = [part for part in config['partitions'] if part['absorb']]

    # spread out the blocks
    _dist_blocks(leftover_blocks, sponge_parts)


# return aligned partition size
def _calc_size(part: Dict, size: int) -> int:

    size = SCRAMBLE_BLOCK_WIDTH * \
        int((size + SCRAMBLE_BLOCK_WIDTH - 1) / SCRAMBLE_BLOCK_WIDTH)

    if part["sw_digest"] or part["hw_digest"]:
        size += DIGEST_SIZE

    return size


def _validate_part(part: Dict, key_names: List[str], is_last: bool):
    '''Validates a partition within the OTP memory map'''
    part.setdefault("name", "unknown_name")
    part.setdefault("variant", "Unbuffered")
    part.setdefault("secret", False)
    part.setdefault("sw_digest", False)
    part.setdefault("hw_digest", False)
    part.setdefault("write_lock", "none")
    part.setdefault("read_lock", "none")
    part.setdefault("key_sel", "NoKey")
    part.setdefault("absorb", False)
    part.setdefault("iskeymgr_creator", False)
    part.setdefault("iskeymgr_owner", False)
    log.info("Validating partition {}".format(part["name"]))

    # Make sure these are boolean types (simplifies the mako templates)
    part["secret"] = check_bool(part["secret"])
    part["sw_digest"] = check_bool(part["sw_digest"])
    part["hw_digest"] = check_bool(part["hw_digest"])
    part["bkout_type"] = check_bool(part["bkout_type"])
    part["integrity"] = check_bool(part["integrity"])

    # basic checks
    if part["variant"] not in ["Unbuffered", "Buffered", "LifeCycle"]:
        raise RuntimeError("Invalid partition type {}".format(part["variant"]))

    # the DV and HW assumes that the last partition is always the life cycle
    # partition.
    if (part["variant"] == "LifeCycle") != is_last:
        raise RuntimeError("The last partition must always be the life cycle"
                           "partition")

    if part["key_sel"] not in (["NoKey"] + key_names):
        raise RuntimeError("Invalid key sel {}".format(part["key_sel"]))

    if check_bool(part["secret"]) and part["key_sel"] == "NoKey":
        raise RuntimeError(
            "A secret partition needs a key select value other than NoKey")

    if part["write_lock"].lower() not in ["digest", "csr", "none"]:
        raise RuntimeError("Invalid value for write_lock")

    if part["read_lock"].lower() not in ["digest", "csr", "none"]:
        raise RuntimeError("Invalid value for read_lock")

    if part["sw_digest"] and part["hw_digest"]:
        raise RuntimeError(
            "Partition cannot support both a SW and a HW digest at the same time."
        )

    if part["variant"] == "Unbuffered" and part["hw_digest"]:
        raise RuntimeError(
            "Unbuffered partitions with a HW digest are not supported at the moment."
        )

    if part["variant"] == "Buffered" and part["read_lock"].lower() == "csr":
        raise RuntimeError(
            "CSR read lock is only supported for SW partitions.")

    if not part["sw_digest"] and not part["hw_digest"]:
        if part["write_lock"].lower() == "digest" or part["read_lock"].lower(
        ) == "digest":
            raise RuntimeError(
                "A partition can only be write/read lockable if it has a hw or sw digest."
            )

    if not isinstance(part['items'], list):
        raise RuntimeError('the "items" key must contain a list')

    if len(part["items"]) == 0:
        log.warning("Partition does not contain any items.")

    # validate items and calculate partition size if necessary
    size = 0
    for item in part["items"]:
        _validate_item(item, part["variant"] == "Buffered", part["secret"])
        # if any item has key material, we need mark the partition as such
        if item["iskeymgr_creator"]:
            part["iskeymgr_creator"] = True
        elif item["iskeymgr_owner"]:
            part["iskeymgr_owner"] = True

        size += item["size"]

    # Partitions can either hold keymaterial for the creator stage or owner
    # stage, but not both. This is because the two have separate SW write
    # enable signals in HW.
    if part["iskeymgr_creator"] and part["iskeymgr_owner"]:
        raise RuntimeError(
            "Partition {} with key material for the key manager cannot be "
            "associated with the creator AND the owner.".format(part["name"]))

    # if size not previously defined, set it
    if "size" not in part:
        part["size"] = _calc_size(part, size)

    # Make sure this has integer type.
    part["size"] = check_int(part["size"])

    # Make sure partition size is aligned.
    if part["size"] % SCRAMBLE_BLOCK_WIDTH:
        raise RuntimeError(
            f"Partition size must be {SCRAMBLE_BLOCK_WIDTH * 8}-bit aligned")


def _validate_item(item: Dict, buffered: bool, secret: bool):
    '''Validates an item within a partition'''
    item.setdefault("name", "unknown_name")
    item.setdefault("size", "0")
    item.setdefault("isdigest", "false")
    item.setdefault("ismubi", "false")
    item.setdefault("iskeymgr_creator", "false")
    item.setdefault("iskeymgr_owner", "false")

    # make sure these have the correct types
    item["iskeymgr_creator"] = check_bool(item["iskeymgr_creator"])
    item["iskeymgr_owner"] = check_bool(item["iskeymgr_owner"])
    item["isdigest"] = check_bool(item["isdigest"])
    item["ismubi"] = check_bool(item["ismubi"])
    item["size"] = check_int(item["size"])
    item_width = item["size"] * 8

    # Key material can either be for the creator stage or owner stage, but not
    # both. This is because the two have separate SW write enable signals in HW.
    if item["iskeymgr_creator"] and item["iskeymgr_owner"]:
        raise RuntimeError(
            "Key material for {} for sideloading into the key manager cannot be "
            "associated with the creator AND the owner.".format(item["name"]))

    # Key material for the keymgr needs to live in a buffered partition so that
    # it can be sideloaded. The partition should also be secret for
    # confidentiality.
    if item["iskeymgr_creator"] or item["iskeymgr_owner"]:
        if not buffered:
            raise RuntimeError(
                "Key material {} for sideloading into the key manager needs "
                "to be stored in a buffered partition.".format(item["name"]))
        if not secret:
            raise RuntimeError(
                "Key material {} for sideloading into the key manager needs "
                "to be stored in a secret partition.".format(item["name"]))

    # defaults are handled differently in case of mubi
    if item["ismubi"]:
        if not is_width_valid(item_width):
            raise RuntimeError("Mubi value {} has invalid width".format(
                item["name"]))
        # Convert default to correct mubi value
        item.setdefault("inv_default", "false")
        item["inv_default"] = check_bool(item["inv_default"])
        item["inv_default"] = mubi_value_as_int(item["inv_default"],
                                                item_width)
    else:
        # Generate random constant to be used when partition has
        # not been initialized yet or when it is in error state.
        random_or_hexvalue(item, "inv_default", item_width)


def _validate_mmap(config: Dict) -> Dict:
    '''Validate the memory map configuration'''

    # Get valid key names.
    key_names = []
    for key in config["scrambling"]["keys"]:
        key_names.append(key["name"])

    if not isinstance(config['partitions'], list):
        raise RuntimeError('the "partitions" key must contain a list')

    # validate inputs before use
    allocated = 0
    for k, part in enumerate(config["partitions"]):
        _validate_part(part, key_names, k == (len(config["partitions"]) - 1))
        allocated += part['size']

    # distribute unallocated bits
    _dist_unused(config, allocated)

    # Determine offsets and generation dicts
    offset = 0
    part_dict = {}
    for j, part in enumerate(config["partitions"]):

        if part['name'] in part_dict:
            raise RuntimeError('Partition name {} is not unique'.format(
                part['name']))

        part['offset'] = offset
        if check_int(part['offset']) % SCRAMBLE_BLOCK_WIDTH:
            raise RuntimeError(
                f"Partition {part['name']} offset must be "
                f"{SCRAMBLE_BLOCK_WIDTH * 8}-bit aligned")

        log.info("Partition {} at offset {} size {}".format(
            part["name"], part["offset"], part["size"]))

        # Loop over items within a partition
        item_dict = {}
        for k, item in enumerate(part["items"]):
            if item['name'] in item_dict:
                raise RuntimeError('Item name {} is not unique'.format(
                    item['name']))
            item['offset'] = offset
            log.info("> Item {} at offset {} with size {}".format(
                item["name"], offset, item["size"]))
            offset += check_int(item["size"])
            item_dict[item['name']] = k

        # Place digest at the end of a partition.
        if part["sw_digest"] or part["hw_digest"]:
            digest_name = part["name"] + DIGEST_SUFFIX
            if digest_name in item_dict:
                raise RuntimeError(
                    'Digest name {} is not unique'.format(digest_name))
            item_dict[digest_name] = len(part["items"])
            part["items"].append({
                "name":
                digest_name,
                "size":
                DIGEST_SIZE,
                "offset":
                check_int(part["offset"]) + check_int(part["size"]) -
                DIGEST_SIZE,
                "ismubi":
                False,
                "isdigest":
                True,
                "inv_default":
                "<random>",
                "iskeymgr_creator":
                False,
                "iskeymgr_owner":
                False
            })
            # Randomize the digest default.
            random_or_hexvalue(part["items"][-1], "inv_default",
                               DIGEST_SIZE * 8)

            # We always place the digest into the last 64bit word
            # of a partition.
            canonical_offset = (check_int(part["offset"]) +
                                check_int(part["size"]) - DIGEST_SIZE)
            if offset > canonical_offset:
                raise RuntimeError(
                    "Not enough space in partition "
                    "{} to accommodate a digest. Bytes available "
                    "= {}, bytes allocated to items = {}".format(
                        part["name"], part["size"], offset - part["offset"]))

            offset = canonical_offset
            log.info("> Adding digest {} at offset {} with size {}".format(
                digest_name, offset, DIGEST_SIZE))
            offset += DIGEST_SIZE

        # check offsets and size
        if offset > check_int(part["offset"]) + check_int(part["size"]):
            raise RuntimeError("Not enough space in partition "
                               "{} to accommodate all items. Bytes available "
                               "= {}, bytes allocated to items = {}".format(
                                   part["name"], part["size"],
                                   offset - part["offset"]))

        offset = check_int(part["offset"]) + check_int(part["size"])

        part_dict.setdefault(part['name'], {'index': j, 'items': item_dict})

    if offset > config["otp"]["size"]:
        raise RuntimeError(
            "OTP is not big enough to store all partitions. "
            "Bytes available {}, bytes required {}", config["otp"]["size"],
            offset)

    log.info("Total number of partitions: {}".format(len(
        config["partitions"])))
    log.info("Bytes available in OTP: {}".format(config["otp"]["size"]))
    log.info("Bytes required for partitions: {}".format(offset))

    # return the partition/item index dict
    return part_dict


class OtpMemMap():

    # This holds the config dict.
    config = {}
    # This holds the partition/item index dict for fast access.
    part_dict = {}

    def __init__(self, config):

        log.info('')
        log.info('Parse and translate OTP memory map.')
        log.info('')

        if "seed" not in config:
            raise RuntimeError("Missing seed in configuration.")

        config["seed"] = check_int(config["seed"])

        # Initialize RNG.
        sp.reseed(OTP_SEED_DIVERSIFIER + int(config['seed']))
        log.info('Seed: {0:x}'.format(config['seed']))
        log.info('')

        if "otp" not in config:
            raise RuntimeError("Missing otp configuration.")
        if "scrambling" not in config:
            raise RuntimeError("Missing scrambling configuration.")
        if "partitions" not in config:
            raise RuntimeError("Missing partition configuration.")

        # Validate OTP info.
        _validate_otp(config["otp"])
        # Validate scrambling info.
        _validate_scrambling(config["scrambling"])
        # Validate memory map.
        self.part_dict = _validate_mmap(config)

        self.config = config

        log.info('')
        log.info('Successfully parsed and translated OTP memory map.')
        log.info('')

    @classmethod
    def from_mmap_path(cls, mmap_path: Path, seed: int = None) -> 'OtpMemMap':
        try:
            with open(mmap_path, 'r') as infile:
                config = hjson.load(infile)
        except OSError as e:
            log.error(f"Failed to open file: {e}")
            exit(1)
        except Exception as e:
            log.error(f"Some error loading {mmap_path} into hjson: {e}")
            exit(1)

        # If specified, override the seed for random netlist constant
        # computation.
        if seed:
            log.warning('Commandline override of seed with {}.'.format(seed))
            config['seed'] = seed
        # Otherwise we make sure a seed exists in the HJSON config file.
        elif 'seed' not in config:
            log.error('Seed not found in configuration HJSON.')
            exit(1)

        try:
            otp_mmap = cls(config)
        except RuntimeError as err:
            log.error(err)
            exit(1)
        return otp_mmap

    def create_partitions_table(self) -> str:
        header = [
            "Partition", "Secret", "Buffered", "Integrity", "WR Lockable",
            "RD Lockable", "Description"
        ]
        table = [header]
        colalign = ("center", ) * len(header[:-1]) + ("left", )
        for part in self.config["partitions"]:
            is_secret = "yes" if check_bool(part["secret"]) else "no"
            is_buffered = "yes" if part["variant"] in [
                "Buffered", "LifeCycle"
            ] else "no"
            wr_lockable = "no"
            if part["write_lock"].lower() in ["csr", "digest"]:
                wr_lockable = "yes (" + part["write_lock"] + ")"
            rd_lockable = "no"
            if part["read_lock"].lower() in ["csr", "digest"]:
                rd_lockable = "yes (" + part["read_lock"] + ")"
            integrity = "no"
            if part["integrity"]:
                integrity = "yes"
            desc = part["desc"]
            row = [
                part["name"], is_secret, is_buffered, integrity, wr_lockable,
                rd_lockable, desc
            ]
            table.append(row)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def create_mmap_table(self) -> str:
        header = [
            "Index", "Partition", "Size [B]", "Access Granule", "Item",
            "Byte Address", "Size [B]"
        ]
        table = [header]
        colalign = ("center", ) * len(header)

        for k, part in enumerate(self.config["partitions"]):
            for j, item in enumerate(part["items"]):
                granule = "64bit" if check_bool(part["secret"]) else "32bit"

                if check_bool(item["isdigest"]):
                    granule = "64bit"
                    name = "[{}](#Reg_{}_0)".format(item["name"],
                                                    item["name"].lower())
                else:
                    name = item["name"]

                if j == 0:
                    row = [str(k), part["name"], str(part["size"]), granule]
                else:
                    row = ["", "", "", granule]

                row.extend([
                    name, "0x{:03X}".format(check_int(item["offset"])),
                    str(item["size"])
                ])

                table.append(row)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def create_description_table(self) -> str:
        header = ["Partition", "Item", "Size [B]", "Description"]
        table = [header]
        # Everything column center aligned, except the descriptions.
        colalign = ["center"] * len(header)
        colalign[-1] = "left"

        for k, part in enumerate(self.config["partitions"]):
            for j, item in enumerate(part["items"]):
                name = None
                if check_bool(item["isdigest"]):
                    continue
                else:
                    name = item["name"]

                if j == 0:
                    row = [part["name"]]
                else:
                    row = [""]
                desc = " ".join(item.get("desc", "").split("\n"))
                row.extend([name, str(item["size"]), desc])

                table.append(row)

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def create_digests_table(self) -> str:
        header = ["Digest Name", " Affected Partition", "Calculated by HW"]
        table = [header]
        colalign = ("center", ) * len(header)

        for part in self.config["partitions"]:
            if check_bool(part["hw_digest"]) or check_bool(part["sw_digest"]):
                is_hw_digest = "yes" if check_bool(part["hw_digest"]) else "no"
                for item in part["items"]:
                    if check_bool(item["isdigest"]):
                        name = "[{}](#Reg_{}_0)".format(
                            item["name"], item["name"].lower())
                        row = [name, part["name"], is_hw_digest]
                        table.append(row)
                        break
                else:
                    raise RuntimeError(
                        "Partition with digest does not contain a digest item")

        return tabulate(table,
                        headers="firstrow",
                        tablefmt="pipe",
                        colalign=colalign)

    def get_part(self, part_name) -> str:
        ''' Get partition by name, return None if it does not exist'''
        entry = self.part_dict.get(part_name)
        return (None if entry is None else
                self.config['partitions'][entry['index']])

    def get_item(self, part_name, item_name) -> str:
        ''' Get item by name, return None if it does not exist'''
        entry = self.part_dict.get(part_name)
        if entry is not None:
            idx = entry['items'].get(item_name, None)
            return (None if idx is None else
                    self.config['partitions'][entry['index']]['items'][idx])
        else:
            return None
