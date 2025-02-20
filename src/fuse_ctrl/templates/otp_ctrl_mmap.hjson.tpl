// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Use the gen-otp-mmap.py script to update dependent files (like documentation
// tables the comportable hjson and metadata SV package):

{
    // 256 bit seed to be used for generation of partition item default values.
    // Can be overridden on the command line with the --seed switch.
    seed: "36021179872380457113239299468132194022238108125576166239904535336103582949069"

    otp: {
        width: "2", // bytes
        depth: "2048"
    }

    // Definition of scrambling and digest constants and keys.
    scrambling: {
        key_size:  "16",
        iv_size:   "8",
        cnst_size: "16",
        keys: [
            {
                name:  "SecretTestUnlockKey",
                value: "<random>",
            },        
            {
                name:  "SecretManufKey",
                value: "<random>",
            },
            {
                name:  "SecretProdKey0",
                value: "<random>",
            },
            {
                name:  "SecretProdKey1",
                value: "<random>",
            },
            {
                name:  "SecretProdKey2",
                value: "<random>",
            },
            {
                name:  "SecretProdKey3",
                value: "<random>",
            },
% if num_vendor_fuses > 0:
            {
                name:  "VendorSecretProdKey",
                value: "<random>",
            },
% endif      
            {
                name:  "SecretLifeCycleTransitionKey",
                value: "<random>",
            },
        ]
        digests: [
            // This is the consistency digest used by all partitions.
            {
                name:       "CnstyDigest",
                iv_value:   "<random>",
                cnst_value: "<random>",
            },
        ]
    }

    // The enumeration order below defines the address map of the OTP controller,
    // if the offsets are not defined explicitly via the "offset" key.
    // Note that the digest items are added automatically to the address map.
    partitions: [
        {
            name:       "SECRET_TEST_UNLOCK_PARTITION",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretTestUnlockKey",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN",
                    size: "16",
                    desc: '''
                    Secret value for manufacturing debug unlock authorization.
                    '''
                },                
            ],
            desc: '''Secret manufacturing partition.
            '''
        },
        {
            name:       "SECRET_MANUF_PARTITION",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretManufKey",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_UDS_SEED",
                    inv_default: "<random>",
                    size: "64",
                    desc: '''
                    DICE Unique Device Secret Seed.
                    This seed is unique per device. The seed is scrambled using an obfuscation function.
                    '''
                },            
            ],
            desc: '''Secret manufacturing partition.
            '''
        },
        {
            name:       "SECRET_PROD_PARTITION_0",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretProdKey0",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_FIELD_ENTROPY_0",
                    inv_default: "<random>",
                    size: "8",
                    desc: '''
                    Field entropy chunk 0.
                    Field-programmable by the owner, used to hedge against UDS disclosure in the supply chain.
                    '''
                },
            ],
            desc: '''Secret production partition 0.
            '''
        },
        {
            name:       "SECRET_PROD_PARTITION_1",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretProdKey1",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_FIELD_ENTROPY_1",
                    inv_default: "<random>",
                    size: "8",
                    desc: '''
                    Field entropy chunk 1.
                    Field-programmable by the owner, used to hedge against UDS disclosure in the supply chain.
                    '''
                },
            ],
            desc: '''Secret production partition 1.
            '''
        },
        {
            name:       "SECRET_PROD_PARTITION_2",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretProdKey2",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_FIELD_ENTROPY_2",
                    inv_default: "<random>",
                    size: "8",
                    desc: '''
                    Field entropy chunk 2.
                    Field-programmable by the owner, used to hedge against UDS disclosure in the supply chain.
                    '''
                },
            ],
            desc: '''Secret production partition 2.
            '''
        },
        {
            name:       "SECRET_PROD_PARTITION_3",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretProdKey3",
            integrity:  true,
            bkout_type: true,
            items: [
                {
                    name: "CPTRA_CORE_FIELD_ENTROPY_3",
                    inv_default: "<random>",
                    size: "8",
                    desc: '''
                    Field entropy chunk 3.
                    Field-programmable by the owner, used to hedge against UDS disclosure in the supply chain.
                    '''
                },
            ],
            desc: '''Secret production partition 3.
            '''
        },
        {
            name:       "SW_MANUF_PARTITION",
            variant:    "Unbuffered",
            absorb:     true,
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  true,
            bkout_type: false,
            items: [
                {
                    name: "CPTRA_CORE_ANTI_ROLLBACK_DISABLE",
                    size: "1",
                    desc: '''
                    Disables anti-rollback support from Caliptra.
                    For example, if a Platform RoT is managing FW storage and anti-rollback protection external to the SoC.
                    '''
                },
                {
                    name: "CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR",
                    size: "96",
                    desc: '''
                    IDevID Certificate Generation Attributes.
                    See IDevID certificate section. Caliptra only uses 352 bits. Integrator is not required
                    to back the remaining 416 bits with physical fuses.
                    '''
                },
                {
                    name: "CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER",
                    size: "16",
                    desc: '''
                    Spare bits for Vendor IDevID provisioner CA identifiers.
                    Caliptra does not use these bits. Integrator is not required to back these with physical fuses.
                    '''
                },
                {
                    name: "CPTRA_CORE_SOC_STEPPING_ID",
                    size: "2",
                    desc: '''
                    Identifier assigned by vendor to differentiate silicon steppings.
                    '''
                },
                {
                    name: "CPTRA_SS_PROD_DEBUG_UNLOCK_PKS",
                    size: "512",
                    desc: '''
                    There are 8 different debug levels in production state.
                    Thus, we need one 512-bit location for hash of each of public keys.
                    '''
                },
            ],
            desc: '''Software manufacturing partition.
            '''
        },
        {
            name:       "SECRET_LC_TRANSITION_PARTITION",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "SecretLifeCycleTransitionKey",
            integrity:  true,
            bkout_type: false,
            items: [
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_0",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_1",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_2",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_3",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_4",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_5",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_6",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_UNLOCK_TOKEN_7",
                    inv_default: "<random>",
                    size: "16"
                },
                {
                    name: "CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN",
                    inv_default: "<random>",
                    size: "16",
                    desc: '''
                    Used to transition the device from TEST_EXIT to MANUF state..
                    '''
                },
                {
                    name: "CPTRA_SS_MANUF_TO_PROD_TOKEN",
                    inv_default: "<random>",
                    size: "16",
                    desc: '''
                    Used to transition the device from MANUF to PROD state.
                    '''
                },
               {
                    name: "CPTRA_SS_PROD_TO_PROD_END_TOKEN",
                    inv_default: "<random>",
                    size: "16",
                    desc: '''
                    Used to transition the device from PROD to PROD_END state.
                    '''
                },                                    
            ],
            desc: '''Secret life-cycle unlock token partition.
            '''
        },
        {
            name:       "SVN_PARTITION",
            variant:    "Unbuffered",
            absorb:     false,
            secret:     false,
            sw_digest:  false,
            hw_digest:  false,
            write_lock: "None",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            // This is a strike counter, hence we need to disable ECC integrity for this to work.
            // Integrity is handled at a higher level by SW as described below.
            integrity:  false,
            bkout_type: false,
            items: [
                {
                    name: "CPTRA_CORE_FMC_KEY_MANIFEST_SVN",
                    size: "4",
                    desc: '''
                    FMC security version number.
                    '''
                },
                {
                    name: "CPTRA_CORE_RUNTIME_SVN",
                    size: "16",
                    desc: '''
                    Runtime firmware security version number.
                    '''
                },
                {
                    name: "CPTRA_CORE_SOC_MANIFEST_SVN",
                    size: "16",
                    desc: '''
                    One-hot encoded value for the SOC authorization manifest minimum supported SVN.
                    '''
                },
                {
                    name: "CPTRA_CORE_SOC_MANIFEST_MAX_SVN",
                    size: "1",
                    desc: '''
                    Maximum value for the SOC authorization manifest SVN..
                    '''
                },                   
            ],
            desc: '''SVN Partition.
            '''
        },
        {
            name:       "VENDOR_TEST_PARTITION",
            variant:    "Unbuffered",
            size:       "64", // in bytes
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  false, // Do not use integrity (ECC) on this partition.
            bkout_type: false, // Do not generate a breakout type for this partition.
            items: [
                {
                    name: "VENDOR_TEST",
                    size: "32",
                    desc: '''
                    This is a partition used to test if FUSE programming is done accordingly.
                    It has 14 32-bit vendor test write location and one 64-bit for their digest values.
                    '''
                }
            ],
            desc: '''Vendor test partition.
            '''
        },
#############################################################
## Start vendor-specific fuses
#############################################################
% if num_vendor_fuses > 0:
        {
            name:       "VENDOR_HASHES_MANUF_PARTITION",
            variant:    "Unbuffered",
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  false, // Do not use integrity (ECC) on this partition.
            bkout_type: false, // Do not generate a breakout type for this partition.
            items: [
                {
                    name: "CPTRA_CORE_VENDOR_PK_HASH_0",
                    size: "48",
                    desc: '''
                    SHA384 hash of the Vendor ECDSA P384 and LMS or MLDSA Public Key Descriptors.
                    '''
                },
                {
                    name:   "CPTRA_CORE_PQC_KEY_TYPE_0",
                    size:   "1",
                    desc: '''
                    One-hot encoded selection of PQC key type for firmware validation. Bit 0 -> MLDSA, Bit 1 -> LMS.
                    '''
                },                         
            ],
            desc: '''Vendor hashes manufacturing partition.
            '''
        },
        {
            name:       "VENDOR_HASHES_PROD_PARTITION",
            variant:    "Unbuffered",
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  false, // Do not use integrity (ECC) on this partition.
            bkout_type: false, // Do not generate a breakout type for this partition.
            items: [    
    % for i in range(1, num_vendor_fuses):               
                {
                    name: "CPTRA_CORE_VENDOR_PK_HASH_${i}",
                    size: "48",
                    desc: '''
                    SHA384 hash of the Vendor ECDSA P384 and LMS or MLDSA Public Key Descriptors.
                    '''
                },
                {
                    name:   "CPTRA_CORE_PQC_KEY_TYPE_${i}",
                    size:   "1",
                    desc: '''
                    One-hot encoded selection of PQC key type for firmware validation. Bit 0 -> MLDSA, Bit 1 -> LMS.
                    '''
                },
    % endfor
                {
                    name:   "CPTRA_CORE_VENDOR_PK_HASH_VALID",
                    size:   "${-(-i // 8)}",
                    desc: '''
                    Once a key is marked valid, anything above should not be able to be written (essentially
                    a volatile lock should be implemented on higher order bits).
                    '''
                },                                          
            ],
            desc: '''Vendor hashes production partition.
            '''
        },
        {
            name:       "VENDOR_REVOCATIONS_PROD_PARTITION",
            variant:    "Unbuffered",
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  false, // Do not use integrity (ECC) on this partition.
            bkout_type: false, // Do not generate a breakout type for this partition.
            items: [
    % for i in range(num_vendor_fuses):  
                {
                    name:   "CPTRA_CORE_ECC_REVOCATION_${i}",
                    size:   "1",
                    desc: '''
                    One-hot encoded list of revoked Vendor ECDSA P384 Public Keys (up to 4 keys).
                    '''
                },
                {
                    name:   "CPTRA_CORE_LMS_REVOCATION_${i}",
                    size:   "4",
                    desc: '''
                    One-hot encoded list of revoked Vendor LMS Public Keys (up to 32 keys).
                    '''
                },
                {
                    name:   "CPTRA_CORE_MLDSA_REVOCATION_${i}",
                    size:   "4",
                    desc: '''
                    One-hot encoded list of revoked Vendor MLDSA Public Keys (up to 4 keys).
                    '''
                },
    % endfor                                  
            ],
            desc: '''Vendor revocations production partition.
            '''
        },
        {
            name:       "VENDOR_SECRET_PROD_PARTITION",
            variant:    "Buffered",
            secret:     true,
            sw_digest:  false,
            hw_digest:  true,
            write_lock: "Digest",
            read_lock:  "Digest",
            key_sel:    "VendorSecretProdKey",
            integrity:  true,
            bkout_type: true,
            items: [
    % for i in range(num_vendor_fuses):
                {
                    name: "CPTRA_SS_VENDOR_SPECIFIC_SECRET_FUSE_${i}",
                    inv_default: "<random>",
                    size: "32",
                    desc: '''Vendor-specific secret fuse ${i}.
                    '''
                },
    % endfor
            ],
            desc: '''Vendor secret production partition.
            '''
        },
        {
            name:       "VENDOR_NON_SECRET_PROD_PARTITION",
            variant:    "Unbuffered",
            absorb:     true,
            secret:     false,
            sw_digest:  true,
            hw_digest:  false,
            write_lock: "Digest",
            read_lock:  "CSR",
            key_sel:    "NoKey",
            integrity:  true,
            bkout_type: false,
            items: [
    % for i in range(num_vendor_fuses):
               {
                    name: "CPTRA_SS_VENDOR_SPECIFIC_NON_SECRET_FUSE_${i}",
                    size: "32",
                    desc: '''Vendor-specific non-secret fuse ${i}.
                    '''
                },
    % endfor
            ],
            desc: '''Vendor non-secret production partition.
            '''
        },
% endif
#############################################################
## End vendor-specific fuses
#############################################################      
        {
            name:       "LIFE_CYCLE",
            variant:    "LifeCycle",
            secret:     false,
            sw_digest:  false,
            hw_digest:  false,
            write_lock: "None",
            read_lock:  "None",
            key_sel:    "NoKey",
            integrity:  true,
            bkout_type: false,
            items: [
                // The life cycle transition count is specified
                // first such that any programming attempt of the life cycle
                // partition through the LCI will always write the transition
                // counter words first when programming an updated state vector.
                // This is an additional safeguard, to the sequencing in the
                // life cycle controller to ensure that the counter is always written
                // before any state update. I.e., the life cycle controller
                // already splits the counter and state updates into two
                // supsequent requests through the LCI, where the first request
                // only contains the updated transition counter, and the second
                // request the updated transition counter and state.
                {
                    name: "LC_TRANSITION_CNT",
                    inv_default: "<random>",
                    size: "48"
                }
                {
                    name: "LC_STATE",
                    inv_default: "<random>",
                    size: "40"
                }
            ],
            desc: '''Lifecycle partition.
            This contains lifecycle transition count and state. This partition
            cannot be locked since the life cycle state needs to advance to RMA
            in-field. Note that while this partition is not marked secret, it
            is not readable nor writeable via the DAI. Only the LC controller
            can access this partition, and even via the LC controller it is not
            possible to read the raw manufacturing life cycle state in encoded
            form, since that encoding is considered a netlist secret. The LC
            controller only exposes a decoded version of this state.
            '''
        },
    ]
}