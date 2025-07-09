// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//



package otp_ctrl_reg_pkg;

  // Param list
  parameter int NumSramKeyReqSlots = 4;
  parameter int OtpByteAddrWidth = 12;
  parameter int NumErrorEntries = 18;
  parameter int NumDaiWords = 2;
  parameter int NumDigestWords = 2;
  parameter int NumSwCfgWindowWords = 1024;
  parameter int NumPart = 16;
  parameter int NumPartUnbuf = 7;
  parameter int NumPartBuf = 9;
  parameter int SwTestUnlockPartitionOffset = 0;
  parameter int SwTestUnlockPartitionSize = 72;
  parameter int CptraSsManufDebugUnlockTokenOffset = 0;
  parameter int CptraSsManufDebugUnlockTokenSize = 64;
  parameter int SwTestUnlockPartitionDigestOffset = 64;
  parameter int SwTestUnlockPartitionDigestSize = 8;
  parameter int SecretManufPartitionOffset = 72;
  parameter int SecretManufPartitionSize = 72;
  parameter int CptraCoreUdsSeedOffset = 72;
  parameter int CptraCoreUdsSeedSize = 64;
  parameter int SecretManufPartitionDigestOffset = 136;
  parameter int SecretManufPartitionDigestSize = 8;
  parameter int SecretProdPartition0Offset = 144;
  parameter int SecretProdPartition0Size = 16;
  parameter int CptraCoreFieldEntropy0Offset = 144;
  parameter int CptraCoreFieldEntropy0Size = 8;
  parameter int SecretProdPartition0DigestOffset = 152;
  parameter int SecretProdPartition0DigestSize = 8;
  parameter int SecretProdPartition1Offset = 160;
  parameter int SecretProdPartition1Size = 16;
  parameter int CptraCoreFieldEntropy1Offset = 160;
  parameter int CptraCoreFieldEntropy1Size = 8;
  parameter int SecretProdPartition1DigestOffset = 168;
  parameter int SecretProdPartition1DigestSize = 8;
  parameter int SecretProdPartition2Offset = 176;
  parameter int SecretProdPartition2Size = 16;
  parameter int CptraCoreFieldEntropy2Offset = 176;
  parameter int CptraCoreFieldEntropy2Size = 8;
  parameter int SecretProdPartition2DigestOffset = 184;
  parameter int SecretProdPartition2DigestSize = 8;
  parameter int SecretProdPartition3Offset = 192;
  parameter int SecretProdPartition3Size = 16;
  parameter int CptraCoreFieldEntropy3Offset = 192;
  parameter int CptraCoreFieldEntropy3Size = 8;
  parameter int SecretProdPartition3DigestOffset = 200;
  parameter int SecretProdPartition3DigestSize = 8;
  parameter int SwManufPartitionOffset = 208;
  parameter int SwManufPartitionSize = 520;
  parameter int CptraCoreAntiRollbackDisableOffset = 208;
  parameter int CptraCoreAntiRollbackDisableSize = 4;
  parameter int CptraCoreIdevidCertIdevidAttrOffset = 212;
  parameter int CptraCoreIdevidCertIdevidAttrSize = 96;
  parameter int SocSpecificIdevidCertificateOffset = 308;
  parameter int SocSpecificIdevidCertificateSize = 4;
  parameter int CptraCoreIdevidManufHsmIdentifierOffset = 312;
  parameter int CptraCoreIdevidManufHsmIdentifierSize = 16;
  parameter int CptraCoreSocSteppingIdOffset = 328;
  parameter int CptraCoreSocSteppingIdSize = 4;
  parameter int CptraSsProdDebugUnlockPks0Offset = 332;
  parameter int CptraSsProdDebugUnlockPks0Size = 48;
  parameter int CptraSsProdDebugUnlockPks1Offset = 380;
  parameter int CptraSsProdDebugUnlockPks1Size = 48;
  parameter int CptraSsProdDebugUnlockPks2Offset = 428;
  parameter int CptraSsProdDebugUnlockPks2Size = 48;
  parameter int CptraSsProdDebugUnlockPks3Offset = 476;
  parameter int CptraSsProdDebugUnlockPks3Size = 48;
  parameter int CptraSsProdDebugUnlockPks4Offset = 524;
  parameter int CptraSsProdDebugUnlockPks4Size = 48;
  parameter int CptraSsProdDebugUnlockPks5Offset = 572;
  parameter int CptraSsProdDebugUnlockPks5Size = 48;
  parameter int CptraSsProdDebugUnlockPks6Offset = 620;
  parameter int CptraSsProdDebugUnlockPks6Size = 48;
  parameter int CptraSsProdDebugUnlockPks7Offset = 668;
  parameter int CptraSsProdDebugUnlockPks7Size = 48;
  parameter int SwManufPartitionDigestOffset = 720;
  parameter int SwManufPartitionDigestSize = 8;
  parameter int SecretLcTransitionPartitionOffset = 728;
  parameter int SecretLcTransitionPartitionSize = 184;
  parameter int CptraSsTestUnlockToken1Offset = 728;
  parameter int CptraSsTestUnlockToken1Size = 16;
  parameter int CptraSsTestUnlockToken2Offset = 744;
  parameter int CptraSsTestUnlockToken2Size = 16;
  parameter int CptraSsTestUnlockToken3Offset = 760;
  parameter int CptraSsTestUnlockToken3Size = 16;
  parameter int CptraSsTestUnlockToken4Offset = 776;
  parameter int CptraSsTestUnlockToken4Size = 16;
  parameter int CptraSsTestUnlockToken5Offset = 792;
  parameter int CptraSsTestUnlockToken5Size = 16;
  parameter int CptraSsTestUnlockToken6Offset = 808;
  parameter int CptraSsTestUnlockToken6Size = 16;
  parameter int CptraSsTestUnlockToken7Offset = 824;
  parameter int CptraSsTestUnlockToken7Size = 16;
  parameter int CptraSsTestExitToManufTokenOffset = 840;
  parameter int CptraSsTestExitToManufTokenSize = 16;
  parameter int CptraSsManufToProdTokenOffset = 856;
  parameter int CptraSsManufToProdTokenSize = 16;
  parameter int CptraSsProdToProdEndTokenOffset = 872;
  parameter int CptraSsProdToProdEndTokenSize = 16;
  parameter int CptraSsRmaTokenOffset = 888;
  parameter int CptraSsRmaTokenSize = 16;
  parameter int SecretLcTransitionPartitionDigestOffset = 904;
  parameter int SecretLcTransitionPartitionDigestSize = 8;
  parameter int SvnPartitionOffset = 912;
  parameter int SvnPartitionSize = 40;
  parameter int CptraCoreFmcKeyManifestSvnOffset = 912;
  parameter int CptraCoreFmcKeyManifestSvnSize = 4;
  parameter int CptraCoreRuntimeSvnOffset = 916;
  parameter int CptraCoreRuntimeSvnSize = 16;
  parameter int CptraCoreSocManifestSvnOffset = 932;
  parameter int CptraCoreSocManifestSvnSize = 16;
  parameter int CptraCoreSocManifestMaxSvnOffset = 948;
  parameter int CptraCoreSocManifestMaxSvnSize = 4;
  parameter int VendorTestPartitionOffset = 952;
  parameter int VendorTestPartitionSize = 64;
  parameter int VendorTestOffset = 952;
  parameter int VendorTestSize = 32;
  parameter int VendorTestPartitionDigestOffset = 1008;
  parameter int VendorTestPartitionDigestSize = 8;
  parameter int VendorHashesManufPartitionOffset = 1016;
  parameter int VendorHashesManufPartitionSize = 64;
  parameter int CptraCoreVendorPkHash0Offset = 1016;
  parameter int CptraCoreVendorPkHash0Size = 48;
  parameter int CptraCorePqcKeyType0Offset = 1064;
  parameter int CptraCorePqcKeyType0Size = 4;
  parameter int VendorHashesManufPartitionDigestOffset = 1072;
  parameter int VendorHashesManufPartitionDigestSize = 8;
  parameter int VendorHashesProdPartitionOffset = 1080;
  parameter int VendorHashesProdPartitionSize = 864;
  parameter int CptraSsOwnerPkHashOffset = 1080;
  parameter int CptraSsOwnerPkHashSize = 48;
  parameter int CptraSsOwnerPqcKeyTypeOffset = 1128;
  parameter int CptraSsOwnerPqcKeyTypeSize = 4;
  parameter int CptraSsOwnerPkHashValidOffset = 1132;
  parameter int CptraSsOwnerPkHashValidSize = 4;
  parameter int CptraCoreVendorPkHash1Offset = 1136;
  parameter int CptraCoreVendorPkHash1Size = 48;
  parameter int CptraCorePqcKeyType1Offset = 1184;
  parameter int CptraCorePqcKeyType1Size = 4;
  parameter int CptraCoreVendorPkHash2Offset = 1188;
  parameter int CptraCoreVendorPkHash2Size = 48;
  parameter int CptraCorePqcKeyType2Offset = 1236;
  parameter int CptraCorePqcKeyType2Size = 4;
  parameter int CptraCoreVendorPkHash3Offset = 1240;
  parameter int CptraCoreVendorPkHash3Size = 48;
  parameter int CptraCorePqcKeyType3Offset = 1288;
  parameter int CptraCorePqcKeyType3Size = 4;
  parameter int CptraCoreVendorPkHash4Offset = 1292;
  parameter int CptraCoreVendorPkHash4Size = 48;
  parameter int CptraCorePqcKeyType4Offset = 1340;
  parameter int CptraCorePqcKeyType4Size = 4;
  parameter int CptraCoreVendorPkHash5Offset = 1344;
  parameter int CptraCoreVendorPkHash5Size = 48;
  parameter int CptraCorePqcKeyType5Offset = 1392;
  parameter int CptraCorePqcKeyType5Size = 4;
  parameter int CptraCoreVendorPkHash6Offset = 1396;
  parameter int CptraCoreVendorPkHash6Size = 48;
  parameter int CptraCorePqcKeyType6Offset = 1444;
  parameter int CptraCorePqcKeyType6Size = 4;
  parameter int CptraCoreVendorPkHash7Offset = 1448;
  parameter int CptraCoreVendorPkHash7Size = 48;
  parameter int CptraCorePqcKeyType7Offset = 1496;
  parameter int CptraCorePqcKeyType7Size = 4;
  parameter int CptraCoreVendorPkHash8Offset = 1500;
  parameter int CptraCoreVendorPkHash8Size = 48;
  parameter int CptraCorePqcKeyType8Offset = 1548;
  parameter int CptraCorePqcKeyType8Size = 4;
  parameter int CptraCoreVendorPkHash9Offset = 1552;
  parameter int CptraCoreVendorPkHash9Size = 48;
  parameter int CptraCorePqcKeyType9Offset = 1600;
  parameter int CptraCorePqcKeyType9Size = 4;
  parameter int CptraCoreVendorPkHash10Offset = 1604;
  parameter int CptraCoreVendorPkHash10Size = 48;
  parameter int CptraCorePqcKeyType10Offset = 1652;
  parameter int CptraCorePqcKeyType10Size = 4;
  parameter int CptraCoreVendorPkHash11Offset = 1656;
  parameter int CptraCoreVendorPkHash11Size = 48;
  parameter int CptraCorePqcKeyType11Offset = 1704;
  parameter int CptraCorePqcKeyType11Size = 4;
  parameter int CptraCoreVendorPkHash12Offset = 1708;
  parameter int CptraCoreVendorPkHash12Size = 48;
  parameter int CptraCorePqcKeyType12Offset = 1756;
  parameter int CptraCorePqcKeyType12Size = 4;
  parameter int CptraCoreVendorPkHash13Offset = 1760;
  parameter int CptraCoreVendorPkHash13Size = 48;
  parameter int CptraCorePqcKeyType13Offset = 1808;
  parameter int CptraCorePqcKeyType13Size = 4;
  parameter int CptraCoreVendorPkHash14Offset = 1812;
  parameter int CptraCoreVendorPkHash14Size = 48;
  parameter int CptraCorePqcKeyType14Offset = 1860;
  parameter int CptraCorePqcKeyType14Size = 4;
  parameter int CptraCoreVendorPkHash15Offset = 1864;
  parameter int CptraCoreVendorPkHash15Size = 48;
  parameter int CptraCorePqcKeyType15Offset = 1912;
  parameter int CptraCorePqcKeyType15Size = 4;
  parameter int CptraCoreVendorPkHashValidOffset = 1916;
  parameter int CptraCoreVendorPkHashValidSize = 16;
  parameter int VendorHashesProdPartitionDigestOffset = 1936;
  parameter int VendorHashesProdPartitionDigestSize = 8;
  parameter int VendorRevocationsProdPartitionOffset = 1944;
  parameter int VendorRevocationsProdPartitionSize = 216;
  parameter int CptraSsOwnerEccRevocationOffset = 1944;
  parameter int CptraSsOwnerEccRevocationSize = 4;
  parameter int CptraSsOwnerLmsRevocationOffset = 1948;
  parameter int CptraSsOwnerLmsRevocationSize = 4;
  parameter int CptraSsOwnerMldsaRevocationOffset = 1952;
  parameter int CptraSsOwnerMldsaRevocationSize = 4;
  parameter int CptraCoreEccRevocation0Offset = 1956;
  parameter int CptraCoreEccRevocation0Size = 4;
  parameter int CptraCoreLmsRevocation0Offset = 1960;
  parameter int CptraCoreLmsRevocation0Size = 4;
  parameter int CptraCoreMldsaRevocation0Offset = 1964;
  parameter int CptraCoreMldsaRevocation0Size = 4;
  parameter int CptraCoreEccRevocation1Offset = 1968;
  parameter int CptraCoreEccRevocation1Size = 4;
  parameter int CptraCoreLmsRevocation1Offset = 1972;
  parameter int CptraCoreLmsRevocation1Size = 4;
  parameter int CptraCoreMldsaRevocation1Offset = 1976;
  parameter int CptraCoreMldsaRevocation1Size = 4;
  parameter int CptraCoreEccRevocation2Offset = 1980;
  parameter int CptraCoreEccRevocation2Size = 4;
  parameter int CptraCoreLmsRevocation2Offset = 1984;
  parameter int CptraCoreLmsRevocation2Size = 4;
  parameter int CptraCoreMldsaRevocation2Offset = 1988;
  parameter int CptraCoreMldsaRevocation2Size = 4;
  parameter int CptraCoreEccRevocation3Offset = 1992;
  parameter int CptraCoreEccRevocation3Size = 4;
  parameter int CptraCoreLmsRevocation3Offset = 1996;
  parameter int CptraCoreLmsRevocation3Size = 4;
  parameter int CptraCoreMldsaRevocation3Offset = 2000;
  parameter int CptraCoreMldsaRevocation3Size = 4;
  parameter int CptraCoreEccRevocation4Offset = 2004;
  parameter int CptraCoreEccRevocation4Size = 4;
  parameter int CptraCoreLmsRevocation4Offset = 2008;
  parameter int CptraCoreLmsRevocation4Size = 4;
  parameter int CptraCoreMldsaRevocation4Offset = 2012;
  parameter int CptraCoreMldsaRevocation4Size = 4;
  parameter int CptraCoreEccRevocation5Offset = 2016;
  parameter int CptraCoreEccRevocation5Size = 4;
  parameter int CptraCoreLmsRevocation5Offset = 2020;
  parameter int CptraCoreLmsRevocation5Size = 4;
  parameter int CptraCoreMldsaRevocation5Offset = 2024;
  parameter int CptraCoreMldsaRevocation5Size = 4;
  parameter int CptraCoreEccRevocation6Offset = 2028;
  parameter int CptraCoreEccRevocation6Size = 4;
  parameter int CptraCoreLmsRevocation6Offset = 2032;
  parameter int CptraCoreLmsRevocation6Size = 4;
  parameter int CptraCoreMldsaRevocation6Offset = 2036;
  parameter int CptraCoreMldsaRevocation6Size = 4;
  parameter int CptraCoreEccRevocation7Offset = 2040;
  parameter int CptraCoreEccRevocation7Size = 4;
  parameter int CptraCoreLmsRevocation7Offset = 2044;
  parameter int CptraCoreLmsRevocation7Size = 4;
  parameter int CptraCoreMldsaRevocation7Offset = 2048;
  parameter int CptraCoreMldsaRevocation7Size = 4;
  parameter int CptraCoreEccRevocation8Offset = 2052;
  parameter int CptraCoreEccRevocation8Size = 4;
  parameter int CptraCoreLmsRevocation8Offset = 2056;
  parameter int CptraCoreLmsRevocation8Size = 4;
  parameter int CptraCoreMldsaRevocation8Offset = 2060;
  parameter int CptraCoreMldsaRevocation8Size = 4;
  parameter int CptraCoreEccRevocation9Offset = 2064;
  parameter int CptraCoreEccRevocation9Size = 4;
  parameter int CptraCoreLmsRevocation9Offset = 2068;
  parameter int CptraCoreLmsRevocation9Size = 4;
  parameter int CptraCoreMldsaRevocation9Offset = 2072;
  parameter int CptraCoreMldsaRevocation9Size = 4;
  parameter int CptraCoreEccRevocation10Offset = 2076;
  parameter int CptraCoreEccRevocation10Size = 4;
  parameter int CptraCoreLmsRevocation10Offset = 2080;
  parameter int CptraCoreLmsRevocation10Size = 4;
  parameter int CptraCoreMldsaRevocation10Offset = 2084;
  parameter int CptraCoreMldsaRevocation10Size = 4;
  parameter int CptraCoreEccRevocation11Offset = 2088;
  parameter int CptraCoreEccRevocation11Size = 4;
  parameter int CptraCoreLmsRevocation11Offset = 2092;
  parameter int CptraCoreLmsRevocation11Size = 4;
  parameter int CptraCoreMldsaRevocation11Offset = 2096;
  parameter int CptraCoreMldsaRevocation11Size = 4;
  parameter int CptraCoreEccRevocation12Offset = 2100;
  parameter int CptraCoreEccRevocation12Size = 4;
  parameter int CptraCoreLmsRevocation12Offset = 2104;
  parameter int CptraCoreLmsRevocation12Size = 4;
  parameter int CptraCoreMldsaRevocation12Offset = 2108;
  parameter int CptraCoreMldsaRevocation12Size = 4;
  parameter int CptraCoreEccRevocation13Offset = 2112;
  parameter int CptraCoreEccRevocation13Size = 4;
  parameter int CptraCoreLmsRevocation13Offset = 2116;
  parameter int CptraCoreLmsRevocation13Size = 4;
  parameter int CptraCoreMldsaRevocation13Offset = 2120;
  parameter int CptraCoreMldsaRevocation13Size = 4;
  parameter int CptraCoreEccRevocation14Offset = 2124;
  parameter int CptraCoreEccRevocation14Size = 4;
  parameter int CptraCoreLmsRevocation14Offset = 2128;
  parameter int CptraCoreLmsRevocation14Size = 4;
  parameter int CptraCoreMldsaRevocation14Offset = 2132;
  parameter int CptraCoreMldsaRevocation14Size = 4;
  parameter int CptraCoreEccRevocation15Offset = 2136;
  parameter int CptraCoreEccRevocation15Size = 4;
  parameter int CptraCoreLmsRevocation15Offset = 2140;
  parameter int CptraCoreLmsRevocation15Size = 4;
  parameter int CptraCoreMldsaRevocation15Offset = 2144;
  parameter int CptraCoreMldsaRevocation15Size = 4;
  parameter int VendorRevocationsProdPartitionDigestOffset = 2152;
  parameter int VendorRevocationsProdPartitionDigestSize = 8;
  parameter int VendorSecretProdPartitionOffset = 2160;
  parameter int VendorSecretProdPartitionSize = 520;
  parameter int CptraSsVendorSpecificSecretFuse0Offset = 2160;
  parameter int CptraSsVendorSpecificSecretFuse0Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse1Offset = 2192;
  parameter int CptraSsVendorSpecificSecretFuse1Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse2Offset = 2224;
  parameter int CptraSsVendorSpecificSecretFuse2Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse3Offset = 2256;
  parameter int CptraSsVendorSpecificSecretFuse3Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse4Offset = 2288;
  parameter int CptraSsVendorSpecificSecretFuse4Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse5Offset = 2320;
  parameter int CptraSsVendorSpecificSecretFuse5Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse6Offset = 2352;
  parameter int CptraSsVendorSpecificSecretFuse6Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse7Offset = 2384;
  parameter int CptraSsVendorSpecificSecretFuse7Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse8Offset = 2416;
  parameter int CptraSsVendorSpecificSecretFuse8Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse9Offset = 2448;
  parameter int CptraSsVendorSpecificSecretFuse9Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse10Offset = 2480;
  parameter int CptraSsVendorSpecificSecretFuse10Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse11Offset = 2512;
  parameter int CptraSsVendorSpecificSecretFuse11Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse12Offset = 2544;
  parameter int CptraSsVendorSpecificSecretFuse12Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse13Offset = 2576;
  parameter int CptraSsVendorSpecificSecretFuse13Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse14Offset = 2608;
  parameter int CptraSsVendorSpecificSecretFuse14Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse15Offset = 2640;
  parameter int CptraSsVendorSpecificSecretFuse15Size = 32;
  parameter int VendorSecretProdPartitionDigestOffset = 2672;
  parameter int VendorSecretProdPartitionDigestSize = 8;
  parameter int VendorNonSecretProdPartitionOffset = 2680;
  parameter int VendorNonSecretProdPartitionSize = 520;
  parameter int CptraSsVendorSpecificNonSecretFuse0Offset = 2680;
  parameter int CptraSsVendorSpecificNonSecretFuse0Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse1Offset = 2712;
  parameter int CptraSsVendorSpecificNonSecretFuse1Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse2Offset = 2744;
  parameter int CptraSsVendorSpecificNonSecretFuse2Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse3Offset = 2776;
  parameter int CptraSsVendorSpecificNonSecretFuse3Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse4Offset = 2808;
  parameter int CptraSsVendorSpecificNonSecretFuse4Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse5Offset = 2840;
  parameter int CptraSsVendorSpecificNonSecretFuse5Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse6Offset = 2872;
  parameter int CptraSsVendorSpecificNonSecretFuse6Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse7Offset = 2904;
  parameter int CptraSsVendorSpecificNonSecretFuse7Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse8Offset = 2936;
  parameter int CptraSsVendorSpecificNonSecretFuse8Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse9Offset = 2968;
  parameter int CptraSsVendorSpecificNonSecretFuse9Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse10Offset = 3000;
  parameter int CptraSsVendorSpecificNonSecretFuse10Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse11Offset = 3032;
  parameter int CptraSsVendorSpecificNonSecretFuse11Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse12Offset = 3064;
  parameter int CptraSsVendorSpecificNonSecretFuse12Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse13Offset = 3096;
  parameter int CptraSsVendorSpecificNonSecretFuse13Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse14Offset = 3128;
  parameter int CptraSsVendorSpecificNonSecretFuse14Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse15Offset = 3160;
  parameter int CptraSsVendorSpecificNonSecretFuse15Size = 32;
  parameter int VendorNonSecretProdPartitionDigestOffset = 3192;
  parameter int VendorNonSecretProdPartitionDigestSize = 8;
  parameter int LifeCycleOffset = 3200;
  parameter int LifeCycleSize = 88;
  parameter int LcTransitionCntOffset = 3200;
  parameter int LcTransitionCntSize = 48;
  parameter int LcStateOffset = 3248;
  parameter int LcStateSize = 40;
  parameter int NumAlerts = 5;

  // Address widths within the block
  parameter int CoreAw = 13;
  parameter int PrimAw = 5;

  // Number of registers for every interface
  parameter int NumRegsCore = 72;
  parameter int NumRegsPrim = 8;

  ///////////////////////////////////////////////
  // Typedefs for registers for core interface //
  ///////////////////////////////////////////////

  typedef struct packed {
    struct packed {
      logic        q;
    } otp_error;
    struct packed {
      logic        q;
    } otp_operation_done;
  } otp_ctrl_reg2hw_intr_state_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } otp_error;
    struct packed {
      logic        q;
    } otp_operation_done;
  } otp_ctrl_reg2hw_intr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } otp_error;
    struct packed {
      logic        q;
      logic        qe;
    } otp_operation_done;
  } otp_ctrl_reg2hw_intr_test_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } recov_prim_otp_alert;
    struct packed {
      logic        q;
      logic        qe;
    } fatal_prim_otp_alert;
    struct packed {
      logic        q;
      logic        qe;
    } fatal_bus_integ_error;
    struct packed {
      logic        q;
      logic        qe;
    } fatal_check_error;
    struct packed {
      logic        q;
      logic        qe;
    } fatal_macro_error;
  } otp_ctrl_reg2hw_alert_test_reg_t;

  typedef struct packed {
    logic        q;
    logic        qe;
  } otp_ctrl_reg2hw_direct_access_regwen_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } zeroize;
    struct packed {
      logic        q;
      logic        qe;
    } digest;
    struct packed {
      logic        q;
      logic        qe;
    } wr;
    struct packed {
      logic        q;
      logic        qe;
    } rd;
  } otp_ctrl_reg2hw_direct_access_cmd_reg_t;

  typedef struct packed {
    logic [11:0] q;
  } otp_ctrl_reg2hw_direct_access_address_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_direct_access_wdata_mreg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } consistency;
    struct packed {
      logic        q;
      logic        qe;
    } integrity;
  } otp_ctrl_reg2hw_check_trigger_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_check_timeout_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_integrity_check_period_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_consistency_check_period_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_sw_manuf_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_svn_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_vendor_test_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_vendor_hashes_manuf_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_vendor_hashes_prod_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_vendor_revocations_prod_partition_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_vendor_non_secret_prod_partition_read_lock_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_vendor_pk_hash_volatile_lock_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
      logic        de;
    } otp_operation_done;
    struct packed {
      logic        d;
      logic        de;
    } otp_error;
  } otp_ctrl_hw2reg_intr_state_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
    } sw_test_unlock_partition_error;
    struct packed {
      logic        d;
    } secret_manuf_partition_error;
    struct packed {
      logic        d;
    } secret_prod_partition_0_error;
    struct packed {
      logic        d;
    } secret_prod_partition_1_error;
    struct packed {
      logic        d;
    } secret_prod_partition_2_error;
    struct packed {
      logic        d;
    } secret_prod_partition_3_error;
    struct packed {
      logic        d;
    } sw_manuf_partition_error;
    struct packed {
      logic        d;
    } secret_lc_transition_partition_error;
    struct packed {
      logic        d;
    } svn_partition_error;
    struct packed {
      logic        d;
    } vendor_test_partition_error;
    struct packed {
      logic        d;
    } vendor_hashes_manuf_partition_error;
    struct packed {
      logic        d;
    } vendor_hashes_prod_partition_error;
    struct packed {
      logic        d;
    } vendor_revocations_prod_partition_error;
    struct packed {
      logic        d;
    } vendor_secret_prod_partition_error;
    struct packed {
      logic        d;
    } vendor_non_secret_prod_partition_error;
    struct packed {
      logic        d;
    } life_cycle_error;
    struct packed {
      logic        d;
    } dai_error;
    struct packed {
      logic        d;
    } lci_error;
    struct packed {
      logic        d;
    } timeout_error;
    struct packed {
      logic        d;
    } lfsr_fsm_error;
    struct packed {
      logic        d;
    } scrambling_fsm_error;
    struct packed {
      logic        d;
    } bus_integ_error;
    struct packed {
      logic        d;
    } dai_idle;
    struct packed {
      logic        d;
    } check_pending;
  } otp_ctrl_hw2reg_status_reg_t;

  typedef struct packed {
    logic [2:0]  d;
  } otp_ctrl_hw2reg_err_code_mreg_t;

  typedef struct packed {
    logic        d;
  } otp_ctrl_hw2reg_direct_access_regwen_reg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_direct_access_rdata_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_sw_test_unlock_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_manuf_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_prod_partition_0_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_prod_partition_1_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_prod_partition_2_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_prod_partition_3_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_sw_manuf_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret_lc_transition_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_test_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_hashes_manuf_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_hashes_prod_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_revocations_prod_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_secret_prod_partition_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_vendor_non_secret_prod_partition_digest_mreg_t;

  // Register -> HW type for core interface
  typedef struct packed {
    otp_ctrl_reg2hw_intr_state_reg_t intr_state; // [242:241]
    otp_ctrl_reg2hw_intr_enable_reg_t intr_enable; // [240:239]
    otp_ctrl_reg2hw_intr_test_reg_t intr_test; // [238:235]
    otp_ctrl_reg2hw_alert_test_reg_t alert_test; // [234:225]
    otp_ctrl_reg2hw_direct_access_regwen_reg_t direct_access_regwen; // [224:223]
    otp_ctrl_reg2hw_direct_access_cmd_reg_t direct_access_cmd; // [222:215]
    otp_ctrl_reg2hw_direct_access_address_reg_t direct_access_address; // [214:203]
    otp_ctrl_reg2hw_direct_access_wdata_mreg_t [1:0] direct_access_wdata; // [202:139]
    otp_ctrl_reg2hw_check_trigger_reg_t check_trigger; // [138:135]
    otp_ctrl_reg2hw_check_timeout_reg_t check_timeout; // [134:103]
    otp_ctrl_reg2hw_integrity_check_period_reg_t integrity_check_period; // [102:71]
    otp_ctrl_reg2hw_consistency_check_period_reg_t consistency_check_period; // [70:39]
    otp_ctrl_reg2hw_sw_manuf_partition_read_lock_reg_t sw_manuf_partition_read_lock; // [38:38]
    otp_ctrl_reg2hw_svn_partition_read_lock_reg_t svn_partition_read_lock; // [37:37]
    otp_ctrl_reg2hw_vendor_test_partition_read_lock_reg_t
        vendor_test_partition_read_lock; // [36:36]
    otp_ctrl_reg2hw_vendor_hashes_manuf_partition_read_lock_reg_t
        vendor_hashes_manuf_partition_read_lock; // [35:35]
    otp_ctrl_reg2hw_vendor_hashes_prod_partition_read_lock_reg_t
        vendor_hashes_prod_partition_read_lock; // [34:34]
    otp_ctrl_reg2hw_vendor_revocations_prod_partition_read_lock_reg_t
        vendor_revocations_prod_partition_read_lock; // [33:33]
    otp_ctrl_reg2hw_vendor_non_secret_prod_partition_read_lock_reg_t
        vendor_non_secret_prod_partition_read_lock; // [32:32]
    otp_ctrl_reg2hw_vendor_pk_hash_volatile_lock_reg_t vendor_pk_hash_volatile_lock; // [31:0]
  } otp_ctrl_core_reg2hw_t;

  // HW -> register type for core interface
  typedef struct packed {
    otp_ctrl_hw2reg_intr_state_reg_t intr_state; // [1042:1039]
    otp_ctrl_hw2reg_status_reg_t status; // [1038:1015]
    otp_ctrl_hw2reg_err_code_mreg_t [17:0] err_code; // [1014:961]
    otp_ctrl_hw2reg_direct_access_regwen_reg_t direct_access_regwen; // [960:960]
    otp_ctrl_hw2reg_direct_access_rdata_mreg_t [1:0] direct_access_rdata; // [959:896]
    otp_ctrl_hw2reg_sw_test_unlock_partition_digest_mreg_t [1:0]
        sw_test_unlock_partition_digest; // [895:832]
    otp_ctrl_hw2reg_secret_manuf_partition_digest_mreg_t [1:0]
        secret_manuf_partition_digest; // [831:768]
    otp_ctrl_hw2reg_secret_prod_partition_0_digest_mreg_t [1:0]
        secret_prod_partition_0_digest; // [767:704]
    otp_ctrl_hw2reg_secret_prod_partition_1_digest_mreg_t [1:0]
        secret_prod_partition_1_digest; // [703:640]
    otp_ctrl_hw2reg_secret_prod_partition_2_digest_mreg_t [1:0]
        secret_prod_partition_2_digest; // [639:576]
    otp_ctrl_hw2reg_secret_prod_partition_3_digest_mreg_t [1:0]
        secret_prod_partition_3_digest; // [575:512]
    otp_ctrl_hw2reg_sw_manuf_partition_digest_mreg_t [1:0] sw_manuf_partition_digest; // [511:448]
    otp_ctrl_hw2reg_secret_lc_transition_partition_digest_mreg_t [1:0]
        secret_lc_transition_partition_digest; // [447:384]
    otp_ctrl_hw2reg_vendor_test_partition_digest_mreg_t [1:0]
        vendor_test_partition_digest; // [383:320]
    otp_ctrl_hw2reg_vendor_hashes_manuf_partition_digest_mreg_t [1:0]
        vendor_hashes_manuf_partition_digest; // [319:256]
    otp_ctrl_hw2reg_vendor_hashes_prod_partition_digest_mreg_t [1:0]
        vendor_hashes_prod_partition_digest; // [255:192]
    otp_ctrl_hw2reg_vendor_revocations_prod_partition_digest_mreg_t [1:0]
        vendor_revocations_prod_partition_digest; // [191:128]
    otp_ctrl_hw2reg_vendor_secret_prod_partition_digest_mreg_t [1:0]
        vendor_secret_prod_partition_digest; // [127:64]
    otp_ctrl_hw2reg_vendor_non_secret_prod_partition_digest_mreg_t [1:0]
        vendor_non_secret_prod_partition_digest; // [63:0]
  } otp_ctrl_core_hw2reg_t;

  // Register offsets for core interface
  parameter logic [CoreAw-1:0] OTP_CTRL_INTR_STATE_OFFSET = 13'h 0;
  parameter logic [CoreAw-1:0] OTP_CTRL_INTR_ENABLE_OFFSET = 13'h 4;
  parameter logic [CoreAw-1:0] OTP_CTRL_INTR_TEST_OFFSET = 13'h 8;
  parameter logic [CoreAw-1:0] OTP_CTRL_ALERT_TEST_OFFSET = 13'h c;
  parameter logic [CoreAw-1:0] OTP_CTRL_STATUS_OFFSET = 13'h 10;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_0_OFFSET = 13'h 14;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_1_OFFSET = 13'h 18;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_2_OFFSET = 13'h 1c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_3_OFFSET = 13'h 20;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_4_OFFSET = 13'h 24;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_5_OFFSET = 13'h 28;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_6_OFFSET = 13'h 2c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_7_OFFSET = 13'h 30;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_8_OFFSET = 13'h 34;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_9_OFFSET = 13'h 38;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_10_OFFSET = 13'h 3c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_11_OFFSET = 13'h 40;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_12_OFFSET = 13'h 44;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_13_OFFSET = 13'h 48;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_14_OFFSET = 13'h 4c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_15_OFFSET = 13'h 50;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_16_OFFSET = 13'h 54;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_17_OFFSET = 13'h 58;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET = 13'h 5c;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET = 13'h 60;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET = 13'h 64;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET = 13'h 68;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET = 13'h 6c;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET = 13'h 70;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET = 13'h 74;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET = 13'h 78;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TRIGGER_OFFSET = 13'h 7c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_REGWEN_OFFSET = 13'h 80;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TIMEOUT_OFFSET = 13'h 84;
  parameter logic [CoreAw-1:0] OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET = 13'h 88;
  parameter logic [CoreAw-1:0] OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET = 13'h 8c;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_OFFSET = 13'h 90;
  parameter logic [CoreAw-1:0] OTP_CTRL_SVN_PARTITION_READ_LOCK_OFFSET = 13'h 94;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_OFFSET = 13'h 98;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_OFFSET = 13'h 9c;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_OFFSET = 13'h a0;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_OFFSET = 13'h a4;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_OFFSET = 13'h a8;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK_OFFSET = 13'h ac;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0_OFFSET = 13'h b0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1_OFFSET = 13'h b4;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h b8;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h bc;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_OFFSET = 13'h c0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_OFFSET = 13'h c4;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_OFFSET = 13'h c8;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_OFFSET = 13'h cc;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_OFFSET = 13'h d0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_OFFSET = 13'h d4;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_OFFSET = 13'h d8;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_OFFSET = 13'h dc;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h e0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h e4;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_OFFSET = 13'h e8;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_OFFSET = 13'h ec;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_OFFSET = 13'h f0;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_OFFSET = 13'h f4;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h f8;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h fc;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 100;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 104;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 108;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 10c;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 110;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 114;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 118;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 11c;

  // Reset values for hwext registers and their fields for core interface
  parameter logic [1:0] OTP_CTRL_INTR_TEST_RESVAL = 2'h 0;
  parameter logic [0:0] OTP_CTRL_INTR_TEST_OTP_OPERATION_DONE_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_INTR_TEST_OTP_ERROR_RESVAL = 1'h 0;
  parameter logic [4:0] OTP_CTRL_ALERT_TEST_RESVAL = 5'h 0;
  parameter logic [0:0] OTP_CTRL_ALERT_TEST_FATAL_MACRO_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_ALERT_TEST_FATAL_CHECK_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_ALERT_TEST_FATAL_PRIM_OTP_ALERT_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_ALERT_TEST_RECOV_PRIM_OTP_ALERT_RESVAL = 1'h 0;
  parameter logic [23:0] OTP_CTRL_STATUS_RESVAL = 24'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SW_TEST_UNLOCK_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_MANUF_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_PROD_PARTITION_0_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_PROD_PARTITION_1_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_PROD_PARTITION_2_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_PROD_PARTITION_3_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SW_MANUF_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SECRET_LC_TRANSITION_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SVN_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_TEST_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_HASHES_MANUF_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_HASHES_PROD_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_REVOCATIONS_PROD_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_SECRET_PROD_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_VENDOR_NON_SECRET_PROD_PARTITION_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_LIFE_CYCLE_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_DAI_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_LCI_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_TIMEOUT_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_LFSR_FSM_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_BUS_INTEG_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_DAI_IDLE_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CHECK_PENDING_RESVAL = 1'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_0_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_0_ERR_CODE_0_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_1_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_1_ERR_CODE_1_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_2_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_2_ERR_CODE_2_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_3_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_3_ERR_CODE_3_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_4_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_4_ERR_CODE_4_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_5_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_5_ERR_CODE_5_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_6_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_6_ERR_CODE_6_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_7_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_7_ERR_CODE_7_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_8_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_8_ERR_CODE_8_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_9_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_9_ERR_CODE_9_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_10_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_10_ERR_CODE_10_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_11_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_11_ERR_CODE_11_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_12_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_12_ERR_CODE_12_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_13_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_13_ERR_CODE_13_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_14_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_14_ERR_CODE_14_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_15_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_15_ERR_CODE_15_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_16_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_16_ERR_CODE_16_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_17_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_17_ERR_CODE_17_RESVAL = 3'h 0;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_REGWEN_RESVAL = 1'h 1;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_RESVAL = 1'h 1;
  parameter logic [3:0] OTP_CTRL_DIRECT_ACCESS_CMD_RESVAL = 4'h 0;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_CMD_RD_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_CMD_WR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_DIRECT_ACCESS_CMD_ZEROIZE_RESVAL = 1'h 0;
  parameter logic [31:0] OTP_CTRL_DIRECT_ACCESS_RDATA_0_RESVAL = 32'h 0;
  parameter logic [31:0] OTP_CTRL_DIRECT_ACCESS_RDATA_0_DIRECT_ACCESS_RDATA_0_RESVAL = 32'h 0;
  parameter logic [31:0] OTP_CTRL_DIRECT_ACCESS_RDATA_1_RESVAL = 32'h 0;
  parameter logic [31:0] OTP_CTRL_DIRECT_ACCESS_RDATA_1_DIRECT_ACCESS_RDATA_1_RESVAL = 32'h 0;
  parameter logic [1:0] OTP_CTRL_CHECK_TRIGGER_RESVAL = 2'h 0;
  parameter logic [0:0] OTP_CTRL_CHECK_TRIGGER_INTEGRITY_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_RESVAL = 1'h 0;
  parameter logic [31:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0_SW_TEST_UNLOCK_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1_SW_TEST_UNLOCK_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_SECRET_MANUF_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_SECRET_MANUF_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_SECRET_PROD_PARTITION_0_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_SECRET_PROD_PARTITION_0_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_SECRET_PROD_PARTITION_1_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_SECRET_PROD_PARTITION_1_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_SECRET_PROD_PARTITION_2_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_SECRET_PROD_PARTITION_2_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_SECRET_PROD_PARTITION_3_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_SECRET_PROD_PARTITION_3_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_SW_MANUF_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_SW_MANUF_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_VENDOR_TEST_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_VENDOR_TEST_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_RESVAL =
      32'h 0;

  // Window parameters for core interface
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_CFG_WINDOW_OFFSET = 13'h 1000;
  parameter int unsigned       OTP_CTRL_SW_CFG_WINDOW_SIZE   = 'h 1000;
  parameter int unsigned       OTP_CTRL_SW_CFG_WINDOW_IDX    = 0;

  // Register index for core interface
  typedef enum logic [31:0] {
    OTP_CTRL_INTR_STATE,
    OTP_CTRL_INTR_ENABLE,
    OTP_CTRL_INTR_TEST,
    OTP_CTRL_ALERT_TEST,
    OTP_CTRL_STATUS,
    OTP_CTRL_ERR_CODE_0,
    OTP_CTRL_ERR_CODE_1,
    OTP_CTRL_ERR_CODE_2,
    OTP_CTRL_ERR_CODE_3,
    OTP_CTRL_ERR_CODE_4,
    OTP_CTRL_ERR_CODE_5,
    OTP_CTRL_ERR_CODE_6,
    OTP_CTRL_ERR_CODE_7,
    OTP_CTRL_ERR_CODE_8,
    OTP_CTRL_ERR_CODE_9,
    OTP_CTRL_ERR_CODE_10,
    OTP_CTRL_ERR_CODE_11,
    OTP_CTRL_ERR_CODE_12,
    OTP_CTRL_ERR_CODE_13,
    OTP_CTRL_ERR_CODE_14,
    OTP_CTRL_ERR_CODE_15,
    OTP_CTRL_ERR_CODE_16,
    OTP_CTRL_ERR_CODE_17,
    OTP_CTRL_DIRECT_ACCESS_REGWEN,
    OTP_CTRL_DIRECT_ACCESS_CMD,
    OTP_CTRL_DIRECT_ACCESS_ADDRESS,
    OTP_CTRL_DIRECT_ACCESS_WDATA_0,
    OTP_CTRL_DIRECT_ACCESS_WDATA_1,
    OTP_CTRL_DIRECT_ACCESS_RDATA_0,
    OTP_CTRL_DIRECT_ACCESS_RDATA_1,
    OTP_CTRL_CHECK_TRIGGER_REGWEN,
    OTP_CTRL_CHECK_TRIGGER,
    OTP_CTRL_CHECK_REGWEN,
    OTP_CTRL_CHECK_TIMEOUT,
    OTP_CTRL_INTEGRITY_CHECK_PERIOD,
    OTP_CTRL_CONSISTENCY_CHECK_PERIOD,
    OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK,
    OTP_CTRL_SVN_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK,
    OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK,
    OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0,
    OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1,
    OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0,
    OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1,
    OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0,
    OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1,
    OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0,
    OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1,
    OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0,
    OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1,
    OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0,
    OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1,
    OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0,
    OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1,
    OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0,
    OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1,
    OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0,
    OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1
  } otp_ctrl_core_id_e;

  // Register width information to check illegal writes for core interface
  parameter logic [3:0] OTP_CTRL_CORE_PERMIT [72] = '{
    4'b 0001, // index[ 0] OTP_CTRL_INTR_STATE
    4'b 0001, // index[ 1] OTP_CTRL_INTR_ENABLE
    4'b 0001, // index[ 2] OTP_CTRL_INTR_TEST
    4'b 0001, // index[ 3] OTP_CTRL_ALERT_TEST
    4'b 0111, // index[ 4] OTP_CTRL_STATUS
    4'b 0001, // index[ 5] OTP_CTRL_ERR_CODE_0
    4'b 0001, // index[ 6] OTP_CTRL_ERR_CODE_1
    4'b 0001, // index[ 7] OTP_CTRL_ERR_CODE_2
    4'b 0001, // index[ 8] OTP_CTRL_ERR_CODE_3
    4'b 0001, // index[ 9] OTP_CTRL_ERR_CODE_4
    4'b 0001, // index[10] OTP_CTRL_ERR_CODE_5
    4'b 0001, // index[11] OTP_CTRL_ERR_CODE_6
    4'b 0001, // index[12] OTP_CTRL_ERR_CODE_7
    4'b 0001, // index[13] OTP_CTRL_ERR_CODE_8
    4'b 0001, // index[14] OTP_CTRL_ERR_CODE_9
    4'b 0001, // index[15] OTP_CTRL_ERR_CODE_10
    4'b 0001, // index[16] OTP_CTRL_ERR_CODE_11
    4'b 0001, // index[17] OTP_CTRL_ERR_CODE_12
    4'b 0001, // index[18] OTP_CTRL_ERR_CODE_13
    4'b 0001, // index[19] OTP_CTRL_ERR_CODE_14
    4'b 0001, // index[20] OTP_CTRL_ERR_CODE_15
    4'b 0001, // index[21] OTP_CTRL_ERR_CODE_16
    4'b 0001, // index[22] OTP_CTRL_ERR_CODE_17
    4'b 0001, // index[23] OTP_CTRL_DIRECT_ACCESS_REGWEN
    4'b 0001, // index[24] OTP_CTRL_DIRECT_ACCESS_CMD
    4'b 0011, // index[25] OTP_CTRL_DIRECT_ACCESS_ADDRESS
    4'b 1111, // index[26] OTP_CTRL_DIRECT_ACCESS_WDATA_0
    4'b 1111, // index[27] OTP_CTRL_DIRECT_ACCESS_WDATA_1
    4'b 1111, // index[28] OTP_CTRL_DIRECT_ACCESS_RDATA_0
    4'b 1111, // index[29] OTP_CTRL_DIRECT_ACCESS_RDATA_1
    4'b 0001, // index[30] OTP_CTRL_CHECK_TRIGGER_REGWEN
    4'b 0001, // index[31] OTP_CTRL_CHECK_TRIGGER
    4'b 0001, // index[32] OTP_CTRL_CHECK_REGWEN
    4'b 1111, // index[33] OTP_CTRL_CHECK_TIMEOUT
    4'b 1111, // index[34] OTP_CTRL_INTEGRITY_CHECK_PERIOD
    4'b 1111, // index[35] OTP_CTRL_CONSISTENCY_CHECK_PERIOD
    4'b 0001, // index[36] OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK
    4'b 0001, // index[37] OTP_CTRL_SVN_PARTITION_READ_LOCK
    4'b 0001, // index[38] OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK
    4'b 0001, // index[39] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK
    4'b 0001, // index[40] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK
    4'b 0001, // index[41] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK
    4'b 0001, // index[42] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
    4'b 1111, // index[43] OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK
    4'b 1111, // index[44] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0
    4'b 1111, // index[45] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1
    4'b 1111, // index[46] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[47] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[48] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0
    4'b 1111, // index[49] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1
    4'b 1111, // index[50] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0
    4'b 1111, // index[51] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1
    4'b 1111, // index[52] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0
    4'b 1111, // index[53] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1
    4'b 1111, // index[54] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0
    4'b 1111, // index[55] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1
    4'b 1111, // index[56] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[57] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[58] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0
    4'b 1111, // index[59] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1
    4'b 1111, // index[60] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0
    4'b 1111, // index[61] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1
    4'b 1111, // index[62] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[63] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[64] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[65] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[66] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[67] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[68] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[69] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[70] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0
    4'b 1111  // index[71] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1
  };

  ///////////////////////////////////////////////
  // Typedefs for registers for prim interface //
  ///////////////////////////////////////////////

  typedef struct packed {
    struct packed {
      logic [10:0] q;
    } field4;
    struct packed {
      logic [9:0] q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic        q;
    } field1;
    struct packed {
      logic        q;
    } field0;
  } otp_ctrl_reg2hw_csr0_reg_t;

  typedef struct packed {
    struct packed {
      logic [15:0] q;
    } field4;
    struct packed {
      logic        q;
    } field3;
    struct packed {
      logic [6:0]  q;
    } field2;
    struct packed {
      logic        q;
    } field1;
    struct packed {
      logic [6:0]  q;
    } field0;
  } otp_ctrl_reg2hw_csr1_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_csr2_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } field8;
    struct packed {
      logic        q;
    } field7;
    struct packed {
      logic        q;
    } field6;
    struct packed {
      logic        q;
    } field5;
    struct packed {
      logic        q;
    } field4;
    struct packed {
      logic        q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic [9:0] q;
    } field1;
    struct packed {
      logic [2:0]  q;
    } field0;
  } otp_ctrl_reg2hw_csr3_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic        q;
    } field1;
    struct packed {
      logic [9:0] q;
    } field0;
  } otp_ctrl_reg2hw_csr4_reg_t;

  typedef struct packed {
    struct packed {
      logic [15:0] q;
    } field6;
    struct packed {
      logic        q;
    } field5;
    struct packed {
      logic        q;
    } field4;
    struct packed {
      logic [2:0]  q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic [1:0]  q;
    } field1;
    struct packed {
      logic [5:0]  q;
    } field0;
  } otp_ctrl_reg2hw_csr5_reg_t;

  typedef struct packed {
    struct packed {
      logic [15:0] q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic        q;
    } field1;
    struct packed {
      logic [9:0] q;
    } field0;
  } otp_ctrl_reg2hw_csr6_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } field3;
    struct packed {
      logic        q;
    } field2;
    struct packed {
      logic [2:0]  q;
    } field1;
    struct packed {
      logic [5:0]  q;
    } field0;
  } otp_ctrl_reg2hw_csr7_reg_t;

  typedef struct packed {
    struct packed {
      logic [2:0]  d;
      logic        de;
    } field0;
    struct packed {
      logic [9:0] d;
      logic        de;
    } field1;
    struct packed {
      logic        d;
      logic        de;
    } field2;
    struct packed {
      logic        d;
      logic        de;
    } field3;
    struct packed {
      logic        d;
      logic        de;
    } field4;
    struct packed {
      logic        d;
      logic        de;
    } field5;
    struct packed {
      logic        d;
      logic        de;
    } field6;
    struct packed {
      logic        d;
      logic        de;
    } field7;
    struct packed {
      logic        d;
      logic        de;
    } field8;
  } otp_ctrl_hw2reg_csr3_reg_t;

  typedef struct packed {
    struct packed {
      logic [5:0]  d;
      logic        de;
    } field0;
    struct packed {
      logic [1:0]  d;
      logic        de;
    } field1;
    struct packed {
      logic        d;
      logic        de;
    } field2;
    struct packed {
      logic [2:0]  d;
      logic        de;
    } field3;
    struct packed {
      logic        d;
      logic        de;
    } field4;
    struct packed {
      logic        d;
      logic        de;
    } field5;
    struct packed {
      logic [15:0] d;
      logic        de;
    } field6;
  } otp_ctrl_hw2reg_csr5_reg_t;

  typedef struct packed {
    struct packed {
      logic [5:0]  d;
      logic        de;
    } field0;
    struct packed {
      logic [2:0]  d;
      logic        de;
    } field1;
    struct packed {
      logic        d;
      logic        de;
    } field2;
    struct packed {
      logic        d;
      logic        de;
    } field3;
  } otp_ctrl_hw2reg_csr7_reg_t;

  // Register -> HW type for prim interface
  typedef struct packed {
    otp_ctrl_reg2hw_csr0_reg_t csr0; // [158:135]
    otp_ctrl_reg2hw_csr1_reg_t csr1; // [134:103]
    otp_ctrl_reg2hw_csr2_reg_t csr2; // [102:102]
    otp_ctrl_reg2hw_csr3_reg_t csr3; // [101:82]
    otp_ctrl_reg2hw_csr4_reg_t csr4; // [81:69]
    otp_ctrl_reg2hw_csr5_reg_t csr5; // [68:39]
    otp_ctrl_reg2hw_csr6_reg_t csr6; // [38:11]
    otp_ctrl_reg2hw_csr7_reg_t csr7; // [10:0]
  } otp_ctrl_prim_reg2hw_t;

  // HW -> register type for prim interface
  typedef struct packed {
    otp_ctrl_hw2reg_csr3_reg_t csr3; // [80:52]
    otp_ctrl_hw2reg_csr5_reg_t csr5; // [51:15]
    otp_ctrl_hw2reg_csr7_reg_t csr7; // [14:0]
  } otp_ctrl_prim_hw2reg_t;

  // Register offsets for prim interface
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR0_OFFSET = 5'h 0;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR1_OFFSET = 5'h 4;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR2_OFFSET = 5'h 8;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR3_OFFSET = 5'h c;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR4_OFFSET = 5'h 10;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR5_OFFSET = 5'h 14;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR6_OFFSET = 5'h 18;
  parameter logic [PrimAw-1:0] OTP_CTRL_CSR7_OFFSET = 5'h 1c;

  // Register index for prim interface
  typedef enum logic [31:0] {
    OTP_CTRL_CSR0,
    OTP_CTRL_CSR1,
    OTP_CTRL_CSR2,
    OTP_CTRL_CSR3,
    OTP_CTRL_CSR4,
    OTP_CTRL_CSR5,
    OTP_CTRL_CSR6,
    OTP_CTRL_CSR7
  } otp_ctrl_prim_id_e;

  // Register width information to check illegal writes for prim interface
  parameter logic [3:0] OTP_CTRL_PRIM_PERMIT [8] = '{
    4'b 1111, // index[0] OTP_CTRL_CSR0
    4'b 1111, // index[1] OTP_CTRL_CSR1
    4'b 0001, // index[2] OTP_CTRL_CSR2
    4'b 0111, // index[3] OTP_CTRL_CSR3
    4'b 0011, // index[4] OTP_CTRL_CSR4
    4'b 1111, // index[5] OTP_CTRL_CSR5
    4'b 1111, // index[6] OTP_CTRL_CSR6
    4'b 0011  // index[7] OTP_CTRL_CSR7
  };

endpackage
