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
  parameter int NumErrorEntries = 26;
  parameter int NumDaiWords = 2;
  parameter int NumDigestWords = 2;
  parameter int NumSwCfgWindowWords = 1024;
  parameter int NumPart = 24;
  parameter int NumPartUnbuf = 15;
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
  parameter int SwManufPartitionSize = 528;
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
  parameter int SwManufPartitionZerOffset = 728;
  parameter int SwManufPartitionZerSize = 8;
  parameter int SecretLcTransitionPartitionOffset = 736;
  parameter int SecretLcTransitionPartitionSize = 192;
  parameter int CptraSsTestUnlockToken1Offset = 736;
  parameter int CptraSsTestUnlockToken1Size = 16;
  parameter int CptraSsTestUnlockToken2Offset = 752;
  parameter int CptraSsTestUnlockToken2Size = 16;
  parameter int CptraSsTestUnlockToken3Offset = 768;
  parameter int CptraSsTestUnlockToken3Size = 16;
  parameter int CptraSsTestUnlockToken4Offset = 784;
  parameter int CptraSsTestUnlockToken4Size = 16;
  parameter int CptraSsTestUnlockToken5Offset = 800;
  parameter int CptraSsTestUnlockToken5Size = 16;
  parameter int CptraSsTestUnlockToken6Offset = 816;
  parameter int CptraSsTestUnlockToken6Size = 16;
  parameter int CptraSsTestUnlockToken7Offset = 832;
  parameter int CptraSsTestUnlockToken7Size = 16;
  parameter int CptraSsTestExitToManufTokenOffset = 848;
  parameter int CptraSsTestExitToManufTokenSize = 16;
  parameter int CptraSsManufToProdTokenOffset = 864;
  parameter int CptraSsManufToProdTokenSize = 16;
  parameter int CptraSsProdToProdEndTokenOffset = 880;
  parameter int CptraSsProdToProdEndTokenSize = 16;
  parameter int CptraSsRmaTokenOffset = 896;
  parameter int CptraSsRmaTokenSize = 16;
  parameter int SecretLcTransitionPartitionDigestOffset = 912;
  parameter int SecretLcTransitionPartitionDigestSize = 8;
  parameter int SecretLcTransitionPartitionZerOffset = 920;
  parameter int SecretLcTransitionPartitionZerSize = 8;
  parameter int SvnPartitionOffset = 928;
  parameter int SvnPartitionSize = 40;
  parameter int CptraCoreFmcKeyManifestSvnOffset = 928;
  parameter int CptraCoreFmcKeyManifestSvnSize = 4;
  parameter int CptraCoreRuntimeSvnOffset = 932;
  parameter int CptraCoreRuntimeSvnSize = 16;
  parameter int CptraCoreSocManifestSvnOffset = 948;
  parameter int CptraCoreSocManifestSvnSize = 16;
  parameter int CptraCoreSocManifestMaxSvnOffset = 964;
  parameter int CptraCoreSocManifestMaxSvnSize = 4;
  parameter int VendorTestPartitionOffset = 968;
  parameter int VendorTestPartitionSize = 64;
  parameter int VendorTestOffset = 968;
  parameter int VendorTestSize = 32;
  parameter int VendorTestPartitionDigestOffset = 1024;
  parameter int VendorTestPartitionDigestSize = 8;
  parameter int VendorHashesManufPartitionOffset = 1032;
  parameter int VendorHashesManufPartitionSize = 64;
  parameter int CptraCoreVendorPkHash0Offset = 1032;
  parameter int CptraCoreVendorPkHash0Size = 48;
  parameter int CptraCorePqcKeyType0Offset = 1080;
  parameter int CptraCorePqcKeyType0Size = 4;
  parameter int VendorHashesManufPartitionDigestOffset = 1088;
  parameter int VendorHashesManufPartitionDigestSize = 8;
  parameter int VendorHashesProdPartitionOffset = 1096;
  parameter int VendorHashesProdPartitionSize = 864;
  parameter int CptraSsOwnerPkHashOffset = 1096;
  parameter int CptraSsOwnerPkHashSize = 48;
  parameter int CptraSsOwnerPqcKeyTypeOffset = 1144;
  parameter int CptraSsOwnerPqcKeyTypeSize = 4;
  parameter int CptraSsOwnerPkHashValidOffset = 1148;
  parameter int CptraSsOwnerPkHashValidSize = 4;
  parameter int CptraCoreVendorPkHash1Offset = 1152;
  parameter int CptraCoreVendorPkHash1Size = 48;
  parameter int CptraCorePqcKeyType1Offset = 1200;
  parameter int CptraCorePqcKeyType1Size = 4;
  parameter int CptraCoreVendorPkHash2Offset = 1204;
  parameter int CptraCoreVendorPkHash2Size = 48;
  parameter int CptraCorePqcKeyType2Offset = 1252;
  parameter int CptraCorePqcKeyType2Size = 4;
  parameter int CptraCoreVendorPkHash3Offset = 1256;
  parameter int CptraCoreVendorPkHash3Size = 48;
  parameter int CptraCorePqcKeyType3Offset = 1304;
  parameter int CptraCorePqcKeyType3Size = 4;
  parameter int CptraCoreVendorPkHash4Offset = 1308;
  parameter int CptraCoreVendorPkHash4Size = 48;
  parameter int CptraCorePqcKeyType4Offset = 1356;
  parameter int CptraCorePqcKeyType4Size = 4;
  parameter int CptraCoreVendorPkHash5Offset = 1360;
  parameter int CptraCoreVendorPkHash5Size = 48;
  parameter int CptraCorePqcKeyType5Offset = 1408;
  parameter int CptraCorePqcKeyType5Size = 4;
  parameter int CptraCoreVendorPkHash6Offset = 1412;
  parameter int CptraCoreVendorPkHash6Size = 48;
  parameter int CptraCorePqcKeyType6Offset = 1460;
  parameter int CptraCorePqcKeyType6Size = 4;
  parameter int CptraCoreVendorPkHash7Offset = 1464;
  parameter int CptraCoreVendorPkHash7Size = 48;
  parameter int CptraCorePqcKeyType7Offset = 1512;
  parameter int CptraCorePqcKeyType7Size = 4;
  parameter int CptraCoreVendorPkHash8Offset = 1516;
  parameter int CptraCoreVendorPkHash8Size = 48;
  parameter int CptraCorePqcKeyType8Offset = 1564;
  parameter int CptraCorePqcKeyType8Size = 4;
  parameter int CptraCoreVendorPkHash9Offset = 1568;
  parameter int CptraCoreVendorPkHash9Size = 48;
  parameter int CptraCorePqcKeyType9Offset = 1616;
  parameter int CptraCorePqcKeyType9Size = 4;
  parameter int CptraCoreVendorPkHash10Offset = 1620;
  parameter int CptraCoreVendorPkHash10Size = 48;
  parameter int CptraCorePqcKeyType10Offset = 1668;
  parameter int CptraCorePqcKeyType10Size = 4;
  parameter int CptraCoreVendorPkHash11Offset = 1672;
  parameter int CptraCoreVendorPkHash11Size = 48;
  parameter int CptraCorePqcKeyType11Offset = 1720;
  parameter int CptraCorePqcKeyType11Size = 4;
  parameter int CptraCoreVendorPkHash12Offset = 1724;
  parameter int CptraCoreVendorPkHash12Size = 48;
  parameter int CptraCorePqcKeyType12Offset = 1772;
  parameter int CptraCorePqcKeyType12Size = 4;
  parameter int CptraCoreVendorPkHash13Offset = 1776;
  parameter int CptraCoreVendorPkHash13Size = 48;
  parameter int CptraCorePqcKeyType13Offset = 1824;
  parameter int CptraCorePqcKeyType13Size = 4;
  parameter int CptraCoreVendorPkHash14Offset = 1828;
  parameter int CptraCoreVendorPkHash14Size = 48;
  parameter int CptraCorePqcKeyType14Offset = 1876;
  parameter int CptraCorePqcKeyType14Size = 4;
  parameter int CptraCoreVendorPkHash15Offset = 1880;
  parameter int CptraCoreVendorPkHash15Size = 48;
  parameter int CptraCorePqcKeyType15Offset = 1928;
  parameter int CptraCorePqcKeyType15Size = 4;
  parameter int CptraCoreVendorPkHashValidOffset = 1932;
  parameter int CptraCoreVendorPkHashValidSize = 16;
  parameter int VendorHashesProdPartitionDigestOffset = 1952;
  parameter int VendorHashesProdPartitionDigestSize = 8;
  parameter int VendorRevocationsProdPartitionOffset = 1960;
  parameter int VendorRevocationsProdPartitionSize = 216;
  parameter int CptraSsOwnerEccRevocationOffset = 1960;
  parameter int CptraSsOwnerEccRevocationSize = 4;
  parameter int CptraSsOwnerLmsRevocationOffset = 1964;
  parameter int CptraSsOwnerLmsRevocationSize = 4;
  parameter int CptraSsOwnerMldsaRevocationOffset = 1968;
  parameter int CptraSsOwnerMldsaRevocationSize = 4;
  parameter int CptraCoreEccRevocation0Offset = 1972;
  parameter int CptraCoreEccRevocation0Size = 4;
  parameter int CptraCoreLmsRevocation0Offset = 1976;
  parameter int CptraCoreLmsRevocation0Size = 4;
  parameter int CptraCoreMldsaRevocation0Offset = 1980;
  parameter int CptraCoreMldsaRevocation0Size = 4;
  parameter int CptraCoreEccRevocation1Offset = 1984;
  parameter int CptraCoreEccRevocation1Size = 4;
  parameter int CptraCoreLmsRevocation1Offset = 1988;
  parameter int CptraCoreLmsRevocation1Size = 4;
  parameter int CptraCoreMldsaRevocation1Offset = 1992;
  parameter int CptraCoreMldsaRevocation1Size = 4;
  parameter int CptraCoreEccRevocation2Offset = 1996;
  parameter int CptraCoreEccRevocation2Size = 4;
  parameter int CptraCoreLmsRevocation2Offset = 2000;
  parameter int CptraCoreLmsRevocation2Size = 4;
  parameter int CptraCoreMldsaRevocation2Offset = 2004;
  parameter int CptraCoreMldsaRevocation2Size = 4;
  parameter int CptraCoreEccRevocation3Offset = 2008;
  parameter int CptraCoreEccRevocation3Size = 4;
  parameter int CptraCoreLmsRevocation3Offset = 2012;
  parameter int CptraCoreLmsRevocation3Size = 4;
  parameter int CptraCoreMldsaRevocation3Offset = 2016;
  parameter int CptraCoreMldsaRevocation3Size = 4;
  parameter int CptraCoreEccRevocation4Offset = 2020;
  parameter int CptraCoreEccRevocation4Size = 4;
  parameter int CptraCoreLmsRevocation4Offset = 2024;
  parameter int CptraCoreLmsRevocation4Size = 4;
  parameter int CptraCoreMldsaRevocation4Offset = 2028;
  parameter int CptraCoreMldsaRevocation4Size = 4;
  parameter int CptraCoreEccRevocation5Offset = 2032;
  parameter int CptraCoreEccRevocation5Size = 4;
  parameter int CptraCoreLmsRevocation5Offset = 2036;
  parameter int CptraCoreLmsRevocation5Size = 4;
  parameter int CptraCoreMldsaRevocation5Offset = 2040;
  parameter int CptraCoreMldsaRevocation5Size = 4;
  parameter int CptraCoreEccRevocation6Offset = 2044;
  parameter int CptraCoreEccRevocation6Size = 4;
  parameter int CptraCoreLmsRevocation6Offset = 2048;
  parameter int CptraCoreLmsRevocation6Size = 4;
  parameter int CptraCoreMldsaRevocation6Offset = 2052;
  parameter int CptraCoreMldsaRevocation6Size = 4;
  parameter int CptraCoreEccRevocation7Offset = 2056;
  parameter int CptraCoreEccRevocation7Size = 4;
  parameter int CptraCoreLmsRevocation7Offset = 2060;
  parameter int CptraCoreLmsRevocation7Size = 4;
  parameter int CptraCoreMldsaRevocation7Offset = 2064;
  parameter int CptraCoreMldsaRevocation7Size = 4;
  parameter int CptraCoreEccRevocation8Offset = 2068;
  parameter int CptraCoreEccRevocation8Size = 4;
  parameter int CptraCoreLmsRevocation8Offset = 2072;
  parameter int CptraCoreLmsRevocation8Size = 4;
  parameter int CptraCoreMldsaRevocation8Offset = 2076;
  parameter int CptraCoreMldsaRevocation8Size = 4;
  parameter int CptraCoreEccRevocation9Offset = 2080;
  parameter int CptraCoreEccRevocation9Size = 4;
  parameter int CptraCoreLmsRevocation9Offset = 2084;
  parameter int CptraCoreLmsRevocation9Size = 4;
  parameter int CptraCoreMldsaRevocation9Offset = 2088;
  parameter int CptraCoreMldsaRevocation9Size = 4;
  parameter int CptraCoreEccRevocation10Offset = 2092;
  parameter int CptraCoreEccRevocation10Size = 4;
  parameter int CptraCoreLmsRevocation10Offset = 2096;
  parameter int CptraCoreLmsRevocation10Size = 4;
  parameter int CptraCoreMldsaRevocation10Offset = 2100;
  parameter int CptraCoreMldsaRevocation10Size = 4;
  parameter int CptraCoreEccRevocation11Offset = 2104;
  parameter int CptraCoreEccRevocation11Size = 4;
  parameter int CptraCoreLmsRevocation11Offset = 2108;
  parameter int CptraCoreLmsRevocation11Size = 4;
  parameter int CptraCoreMldsaRevocation11Offset = 2112;
  parameter int CptraCoreMldsaRevocation11Size = 4;
  parameter int CptraCoreEccRevocation12Offset = 2116;
  parameter int CptraCoreEccRevocation12Size = 4;
  parameter int CptraCoreLmsRevocation12Offset = 2120;
  parameter int CptraCoreLmsRevocation12Size = 4;
  parameter int CptraCoreMldsaRevocation12Offset = 2124;
  parameter int CptraCoreMldsaRevocation12Size = 4;
  parameter int CptraCoreEccRevocation13Offset = 2128;
  parameter int CptraCoreEccRevocation13Size = 4;
  parameter int CptraCoreLmsRevocation13Offset = 2132;
  parameter int CptraCoreLmsRevocation13Size = 4;
  parameter int CptraCoreMldsaRevocation13Offset = 2136;
  parameter int CptraCoreMldsaRevocation13Size = 4;
  parameter int CptraCoreEccRevocation14Offset = 2140;
  parameter int CptraCoreEccRevocation14Size = 4;
  parameter int CptraCoreLmsRevocation14Offset = 2144;
  parameter int CptraCoreLmsRevocation14Size = 4;
  parameter int CptraCoreMldsaRevocation14Offset = 2148;
  parameter int CptraCoreMldsaRevocation14Size = 4;
  parameter int CptraCoreEccRevocation15Offset = 2152;
  parameter int CptraCoreEccRevocation15Size = 4;
  parameter int CptraCoreLmsRevocation15Offset = 2156;
  parameter int CptraCoreLmsRevocation15Size = 4;
  parameter int CptraCoreMldsaRevocation15Offset = 2160;
  parameter int CptraCoreMldsaRevocation15Size = 4;
  parameter int VendorRevocationsProdPartitionDigestOffset = 2168;
  parameter int VendorRevocationsProdPartitionDigestSize = 8;
  parameter int VendorSecretProdPartitionOffset = 2160;
  parameter int VendorSecretProdPartitionSize = 528;
  parameter int CptraSsVendorSpecificSecretFuse0Offset = 2160;
  parameter int CptraSsVendorSpecificSecretFuse0Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse1Offset = 2208;
  parameter int CptraSsVendorSpecificSecretFuse1Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse2Offset = 2240;
  parameter int CptraSsVendorSpecificSecretFuse2Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse3Offset = 2272;
  parameter int CptraSsVendorSpecificSecretFuse3Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse4Offset = 2304;
  parameter int CptraSsVendorSpecificSecretFuse4Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse5Offset = 2336;
  parameter int CptraSsVendorSpecificSecretFuse5Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse6Offset = 2368;
  parameter int CptraSsVendorSpecificSecretFuse6Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse7Offset = 2400;
  parameter int CptraSsVendorSpecificSecretFuse7Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse8Offset = 2432;
  parameter int CptraSsVendorSpecificSecretFuse8Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse9Offset = 2464;
  parameter int CptraSsVendorSpecificSecretFuse9Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse10Offset = 2496;
  parameter int CptraSsVendorSpecificSecretFuse10Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse11Offset = 2528;
  parameter int CptraSsVendorSpecificSecretFuse11Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse12Offset = 2560;
  parameter int CptraSsVendorSpecificSecretFuse12Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse13Offset = 2592;
  parameter int CptraSsVendorSpecificSecretFuse13Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse14Offset = 2624;
  parameter int CptraSsVendorSpecificSecretFuse14Size = 32;
  parameter int CptraSsVendorSpecificSecretFuse15Offset = 2656;
  parameter int CptraSsVendorSpecificSecretFuse15Size = 32;
  parameter int VendorSecretProdPartitionDigestOffset = 2688;
  parameter int VendorSecretProdPartitionDigestSize = 8;
  parameter int VendorSecretProdPartitionZerOffset = 2680;
  parameter int VendorSecretProdPartitionZerSize = 8;
  parameter int VendorNonSecretProdPartitionOffset = 2688;
  parameter int VendorNonSecretProdPartitionSize = 520;
  parameter int CptraSsVendorSpecificNonSecretFuse0Offset = 2688;
  parameter int CptraSsVendorSpecificNonSecretFuse0Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse1Offset = 2720;
  parameter int CptraSsVendorSpecificNonSecretFuse1Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse2Offset = 2752;
  parameter int CptraSsVendorSpecificNonSecretFuse2Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse3Offset = 2784;
  parameter int CptraSsVendorSpecificNonSecretFuse3Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse4Offset = 2816;
  parameter int CptraSsVendorSpecificNonSecretFuse4Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse5Offset = 2848;
  parameter int CptraSsVendorSpecificNonSecretFuse5Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse6Offset = 2880;
  parameter int CptraSsVendorSpecificNonSecretFuse6Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse7Offset = 2912;
  parameter int CptraSsVendorSpecificNonSecretFuse7Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse8Offset = 2944;
  parameter int CptraSsVendorSpecificNonSecretFuse8Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse9Offset = 2976;
  parameter int CptraSsVendorSpecificNonSecretFuse9Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse10Offset = 3008;
  parameter int CptraSsVendorSpecificNonSecretFuse10Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse11Offset = 3040;
  parameter int CptraSsVendorSpecificNonSecretFuse11Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse12Offset = 3072;
  parameter int CptraSsVendorSpecificNonSecretFuse12Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse13Offset = 3104;
  parameter int CptraSsVendorSpecificNonSecretFuse13Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse14Offset = 3136;
  parameter int CptraSsVendorSpecificNonSecretFuse14Size = 32;
  parameter int CptraSsVendorSpecificNonSecretFuse15Offset = 3168;
  parameter int CptraSsVendorSpecificNonSecretFuse15Size = 32;
  parameter int VendorNonSecretProdPartitionDigestOffset = 3200;
  parameter int VendorNonSecretProdPartitionDigestSize = 8;
  parameter int CptraSsLockHekProd0Offset = 3208;
  parameter int CptraSsLockHekProd0Size = 48;
  parameter int CptraSsLockHekProd0RatchetSeedOffset = 3208;
  parameter int CptraSsLockHekProd0RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd0DigestOffset = 3240;
  parameter int CptraSsLockHekProd0DigestSize = 8;
  parameter int CptraSsLockHekProd0ZerOffset = 3248;
  parameter int CptraSsLockHekProd0ZerSize = 8;
  parameter int CptraSsLockHekProd1Offset = 3256;
  parameter int CptraSsLockHekProd1Size = 48;
  parameter int CptraSsLockHekProd1RatchetSeedOffset = 3256;
  parameter int CptraSsLockHekProd1RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd1DigestOffset = 3288;
  parameter int CptraSsLockHekProd1DigestSize = 8;
  parameter int CptraSsLockHekProd1ZerOffset = 3296;
  parameter int CptraSsLockHekProd1ZerSize = 8;
  parameter int CptraSsLockHekProd2Offset = 3304;
  parameter int CptraSsLockHekProd2Size = 48;
  parameter int CptraSsLockHekProd2RatchetSeedOffset = 3304;
  parameter int CptraSsLockHekProd2RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd2DigestOffset = 3336;
  parameter int CptraSsLockHekProd2DigestSize = 8;
  parameter int CptraSsLockHekProd2ZerOffset = 3344;
  parameter int CptraSsLockHekProd2ZerSize = 8;
  parameter int CptraSsLockHekProd3Offset = 3352;
  parameter int CptraSsLockHekProd3Size = 48;
  parameter int CptraSsLockHekProd3RatchetSeedOffset = 3352;
  parameter int CptraSsLockHekProd3RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd3DigestOffset = 3384;
  parameter int CptraSsLockHekProd3DigestSize = 8;
  parameter int CptraSsLockHekProd3ZerOffset = 3392;
  parameter int CptraSsLockHekProd3ZerSize = 8;
  parameter int CptraSsLockHekProd4Offset = 3400;
  parameter int CptraSsLockHekProd4Size = 48;
  parameter int CptraSsLockHekProd4RatchetSeedOffset = 3400;
  parameter int CptraSsLockHekProd4RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd4DigestOffset = 3432;
  parameter int CptraSsLockHekProd4DigestSize = 8;
  parameter int CptraSsLockHekProd4ZerOffset = 3440;
  parameter int CptraSsLockHekProd4ZerSize = 8;
  parameter int CptraSsLockHekProd5Offset = 3448;
  parameter int CptraSsLockHekProd5Size = 48;
  parameter int CptraSsLockHekProd5RatchetSeedOffset = 3448;
  parameter int CptraSsLockHekProd5RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd5DigestOffset = 3480;
  parameter int CptraSsLockHekProd5DigestSize = 8;
  parameter int CptraSsLockHekProd5ZerOffset = 3488;
  parameter int CptraSsLockHekProd5ZerSize = 8;
  parameter int CptraSsLockHekProd6Offset = 3496;
  parameter int CptraSsLockHekProd6Size = 48;
  parameter int CptraSsLockHekProd6RatchetSeedOffset = 3496;
  parameter int CptraSsLockHekProd6RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd6DigestOffset = 3528;
  parameter int CptraSsLockHekProd6DigestSize = 8;
  parameter int CptraSsLockHekProd6ZerOffset = 3536;
  parameter int CptraSsLockHekProd6ZerSize = 8;
  parameter int CptraSsLockHekProd7Offset = 3544;
  parameter int CptraSsLockHekProd7Size = 48;
  parameter int CptraSsLockHekProd7RatchetSeedOffset = 3544;
  parameter int CptraSsLockHekProd7RatchetSeedSize = 32;
  parameter int CptraSsLockHekProd7DigestOffset = 3576;
  parameter int CptraSsLockHekProd7DigestSize = 8;
  parameter int CptraSsLockHekProd7ZerOffset = 3584;
  parameter int CptraSsLockHekProd7ZerSize = 8;
  parameter int LifeCycleOffset = 3592;
  parameter int LifeCycleSize = 88;
  parameter int LcTransitionCntOffset = 3592;
  parameter int LcTransitionCntSize = 48;
  parameter int LcStateOffset = 3640;
  parameter int LcStateSize = 40;
  parameter int NumAlerts = 5;

  // Address widths within the block
  parameter int CoreAw = 13;
  parameter int PrimAw = 5;

  // Number of registers for every interface
  parameter int NumRegsCore = 105;
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
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_0_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_1_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_2_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_3_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_4_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_5_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_6_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_7_read_lock_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_vendor_pk_hash_volatile_lock_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_ratchet_seed_volatile_lock_reg_t;

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
    } cptra_ss_lock_hek_prod_0_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_1_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_2_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_3_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_4_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_5_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_6_error;
    struct packed {
      logic        d;
    } cptra_ss_lock_hek_prod_7_error;
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

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_0_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_1_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_2_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_3_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_4_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_5_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_6_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_7_digest_mreg_t;

  // Register -> HW type for core interface
  typedef struct packed {
    otp_ctrl_reg2hw_intr_state_reg_t intr_state; // [282:281]
    otp_ctrl_reg2hw_intr_enable_reg_t intr_enable; // [280:279]
    otp_ctrl_reg2hw_intr_test_reg_t intr_test; // [278:275]
    otp_ctrl_reg2hw_alert_test_reg_t alert_test; // [274:265]
    otp_ctrl_reg2hw_direct_access_regwen_reg_t direct_access_regwen; // [264:263]
    otp_ctrl_reg2hw_direct_access_cmd_reg_t direct_access_cmd; // [262:255]
    otp_ctrl_reg2hw_direct_access_address_reg_t direct_access_address; // [254:243]
    otp_ctrl_reg2hw_direct_access_wdata_mreg_t [1:0] direct_access_wdata; // [242:179]
    otp_ctrl_reg2hw_check_trigger_reg_t check_trigger; // [178:175]
    otp_ctrl_reg2hw_check_timeout_reg_t check_timeout; // [174:143]
    otp_ctrl_reg2hw_integrity_check_period_reg_t integrity_check_period; // [142:111]
    otp_ctrl_reg2hw_consistency_check_period_reg_t consistency_check_period; // [110:79]
    otp_ctrl_reg2hw_sw_manuf_partition_read_lock_reg_t sw_manuf_partition_read_lock; // [78:78]
    otp_ctrl_reg2hw_svn_partition_read_lock_reg_t svn_partition_read_lock; // [77:77]
    otp_ctrl_reg2hw_vendor_test_partition_read_lock_reg_t
        vendor_test_partition_read_lock; // [76:76]
    otp_ctrl_reg2hw_vendor_hashes_manuf_partition_read_lock_reg_t
        vendor_hashes_manuf_partition_read_lock; // [75:75]
    otp_ctrl_reg2hw_vendor_hashes_prod_partition_read_lock_reg_t
        vendor_hashes_prod_partition_read_lock; // [74:74]
    otp_ctrl_reg2hw_vendor_revocations_prod_partition_read_lock_reg_t
        vendor_revocations_prod_partition_read_lock; // [73:73]
    otp_ctrl_reg2hw_vendor_non_secret_prod_partition_read_lock_reg_t
        vendor_non_secret_prod_partition_read_lock; // [72:72]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_0_read_lock_reg_t
        cptra_ss_lock_hek_prod_0_read_lock; // [71:71]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_1_read_lock_reg_t
        cptra_ss_lock_hek_prod_1_read_lock; // [70:70]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_2_read_lock_reg_t
        cptra_ss_lock_hek_prod_2_read_lock; // [69:69]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_3_read_lock_reg_t
        cptra_ss_lock_hek_prod_3_read_lock; // [68:68]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_4_read_lock_reg_t
        cptra_ss_lock_hek_prod_4_read_lock; // [67:67]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_5_read_lock_reg_t
        cptra_ss_lock_hek_prod_5_read_lock; // [66:66]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_6_read_lock_reg_t
        cptra_ss_lock_hek_prod_6_read_lock; // [65:65]
    otp_ctrl_reg2hw_cptra_ss_lock_hek_prod_7_read_lock_reg_t
        cptra_ss_lock_hek_prod_7_read_lock; // [64:64]
    otp_ctrl_reg2hw_vendor_pk_hash_volatile_lock_reg_t vendor_pk_hash_volatile_lock; // [63:32]
    otp_ctrl_reg2hw_ratchet_seed_volatile_lock_reg_t ratchet_seed_volatile_lock; // [31:0]
  } otp_ctrl_core_reg2hw_t;

  // HW -> register type for core interface
  typedef struct packed {
    otp_ctrl_hw2reg_intr_state_reg_t intr_state; // [1586:1583]
    otp_ctrl_hw2reg_status_reg_t status; // [1582:1551]
    otp_ctrl_hw2reg_err_code_mreg_t [25:0] err_code; // [1550:1473]
    otp_ctrl_hw2reg_direct_access_regwen_reg_t direct_access_regwen; // [1472:1472]
    otp_ctrl_hw2reg_direct_access_rdata_mreg_t [1:0] direct_access_rdata; // [1471:1408]
    otp_ctrl_hw2reg_sw_test_unlock_partition_digest_mreg_t [1:0]
        sw_test_unlock_partition_digest; // [1407:1344]
    otp_ctrl_hw2reg_secret_manuf_partition_digest_mreg_t [1:0]
        secret_manuf_partition_digest; // [1343:1280]
    otp_ctrl_hw2reg_secret_prod_partition_0_digest_mreg_t [1:0]
        secret_prod_partition_0_digest; // [1279:1216]
    otp_ctrl_hw2reg_secret_prod_partition_1_digest_mreg_t [1:0]
        secret_prod_partition_1_digest; // [1215:1152]
    otp_ctrl_hw2reg_secret_prod_partition_2_digest_mreg_t [1:0]
        secret_prod_partition_2_digest; // [1151:1088]
    otp_ctrl_hw2reg_secret_prod_partition_3_digest_mreg_t [1:0]
        secret_prod_partition_3_digest; // [1087:1024]
    otp_ctrl_hw2reg_sw_manuf_partition_digest_mreg_t [1:0] sw_manuf_partition_digest; // [1023:960]
    otp_ctrl_hw2reg_secret_lc_transition_partition_digest_mreg_t [1:0]
        secret_lc_transition_partition_digest; // [959:896]
    otp_ctrl_hw2reg_vendor_test_partition_digest_mreg_t [1:0]
        vendor_test_partition_digest; // [895:832]
    otp_ctrl_hw2reg_vendor_hashes_manuf_partition_digest_mreg_t [1:0]
        vendor_hashes_manuf_partition_digest; // [831:768]
    otp_ctrl_hw2reg_vendor_hashes_prod_partition_digest_mreg_t [1:0]
        vendor_hashes_prod_partition_digest; // [767:704]
    otp_ctrl_hw2reg_vendor_revocations_prod_partition_digest_mreg_t [1:0]
        vendor_revocations_prod_partition_digest; // [703:640]
    otp_ctrl_hw2reg_vendor_secret_prod_partition_digest_mreg_t [1:0]
        vendor_secret_prod_partition_digest; // [639:576]
    otp_ctrl_hw2reg_vendor_non_secret_prod_partition_digest_mreg_t [1:0]
        vendor_non_secret_prod_partition_digest; // [575:512]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_0_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_0_digest; // [511:448]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_1_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_1_digest; // [447:384]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_2_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_2_digest; // [383:320]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_3_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_3_digest; // [319:256]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_4_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_4_digest; // [255:192]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_5_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_5_digest; // [191:128]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_6_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_6_digest; // [127:64]
    otp_ctrl_hw2reg_cptra_ss_lock_hek_prod_7_digest_mreg_t [1:0]
        cptra_ss_lock_hek_prod_7_digest; // [63:0]
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
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_18_OFFSET = 13'h 5c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_19_OFFSET = 13'h 60;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_20_OFFSET = 13'h 64;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_21_OFFSET = 13'h 68;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_22_OFFSET = 13'h 6c;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_23_OFFSET = 13'h 70;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_24_OFFSET = 13'h 74;
  parameter logic [CoreAw-1:0] OTP_CTRL_ERR_CODE_25_OFFSET = 13'h 78;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET = 13'h 7c;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET = 13'h 80;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET = 13'h 84;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET = 13'h 88;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET = 13'h 8c;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET = 13'h 90;
  parameter logic [CoreAw-1:0] OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET = 13'h 94;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET = 13'h 98;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TRIGGER_OFFSET = 13'h 9c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_REGWEN_OFFSET = 13'h a0;
  parameter logic [CoreAw-1:0] OTP_CTRL_CHECK_TIMEOUT_OFFSET = 13'h a4;
  parameter logic [CoreAw-1:0] OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET = 13'h a8;
  parameter logic [CoreAw-1:0] OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET = 13'h ac;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_OFFSET = 13'h b0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SVN_PARTITION_READ_LOCK_OFFSET = 13'h b4;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_OFFSET = 13'h b8;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_OFFSET = 13'h bc;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_OFFSET = 13'h c0;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_OFFSET = 13'h c4;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_OFFSET = 13'h c8;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_READ_LOCK_OFFSET = 13'h cc;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_READ_LOCK_OFFSET = 13'h d0;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_READ_LOCK_OFFSET = 13'h d4;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_READ_LOCK_OFFSET = 13'h d8;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_READ_LOCK_OFFSET = 13'h dc;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_READ_LOCK_OFFSET = 13'h e0;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_READ_LOCK_OFFSET = 13'h e4;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_READ_LOCK_OFFSET = 13'h e8;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK_OFFSET = 13'h ec;
  parameter logic [CoreAw-1:0] OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK_OFFSET = 13'h f0;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0_OFFSET = 13'h f4;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1_OFFSET = 13'h f8;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h fc;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h 100;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_OFFSET = 13'h 104;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_OFFSET = 13'h 108;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_OFFSET = 13'h 10c;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_OFFSET = 13'h 110;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_OFFSET = 13'h 114;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_OFFSET = 13'h 118;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_OFFSET = 13'h 11c;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_OFFSET = 13'h 120;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h 124;
  parameter logic [CoreAw-1:0] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h 128;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_OFFSET = 13'h 12c;
  parameter logic [CoreAw-1:0] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_OFFSET = 13'h 130;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_OFFSET = 13'h 134;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_OFFSET = 13'h 138;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_OFFSET = 13'h 13c;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_OFFSET = 13'h 140;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 144;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 148;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 14c;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 150;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 154;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 158;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_OFFSET = 13'h 15c;
  parameter logic [CoreAw-1:0] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_OFFSET = 13'h 160;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0_OFFSET = 13'h 164;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1_OFFSET = 13'h 168;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0_OFFSET = 13'h 16c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1_OFFSET = 13'h 170;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0_OFFSET = 13'h 174;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1_OFFSET = 13'h 178;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0_OFFSET = 13'h 17c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1_OFFSET = 13'h 180;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0_OFFSET = 13'h 184;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1_OFFSET = 13'h 188;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0_OFFSET = 13'h 18c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1_OFFSET = 13'h 190;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0_OFFSET = 13'h 194;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1_OFFSET = 13'h 198;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0_OFFSET = 13'h 19c;
  parameter logic [CoreAw-1:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1_OFFSET = 13'h 1a0;

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
  parameter logic [31:0] OTP_CTRL_STATUS_RESVAL = 32'h 0;
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
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_0_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_1_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_2_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_3_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_4_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_5_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_6_ERROR_RESVAL = 1'h 0;
  parameter logic [0:0] OTP_CTRL_STATUS_CPTRA_SS_LOCK_HEK_PROD_7_ERROR_RESVAL = 1'h 0;
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
  parameter logic [2:0] OTP_CTRL_ERR_CODE_18_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_18_ERR_CODE_18_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_19_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_19_ERR_CODE_19_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_20_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_20_ERR_CODE_20_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_21_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_21_ERR_CODE_21_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_22_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_22_ERR_CODE_22_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_23_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_23_ERR_CODE_23_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_24_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_24_ERR_CODE_24_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_25_RESVAL = 3'h 0;
  parameter logic [2:0] OTP_CTRL_ERR_CODE_25_ERR_CODE_25_RESVAL = 3'h 0;
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
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0_RESVAL =
      32'h 0;
  parameter logic [31:0] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1_RESVAL = 32'h 0;
  parameter logic [31:0]
      OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1_RESVAL =
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
    OTP_CTRL_ERR_CODE_18,
    OTP_CTRL_ERR_CODE_19,
    OTP_CTRL_ERR_CODE_20,
    OTP_CTRL_ERR_CODE_21,
    OTP_CTRL_ERR_CODE_22,
    OTP_CTRL_ERR_CODE_23,
    OTP_CTRL_ERR_CODE_24,
    OTP_CTRL_ERR_CODE_25,
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
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_READ_LOCK,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_READ_LOCK,
    OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK,
    OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK,
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
    OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0,
    OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1
  } otp_ctrl_core_id_e;

  // Register width information to check illegal writes for core interface
  parameter logic [3:0] OTP_CTRL_CORE_PERMIT [105] = '{
    4'b 0001, // index[  0] OTP_CTRL_INTR_STATE
    4'b 0001, // index[  1] OTP_CTRL_INTR_ENABLE
    4'b 0001, // index[  2] OTP_CTRL_INTR_TEST
    4'b 0001, // index[  3] OTP_CTRL_ALERT_TEST
    4'b 1111, // index[  4] OTP_CTRL_STATUS
    4'b 0001, // index[  5] OTP_CTRL_ERR_CODE_0
    4'b 0001, // index[  6] OTP_CTRL_ERR_CODE_1
    4'b 0001, // index[  7] OTP_CTRL_ERR_CODE_2
    4'b 0001, // index[  8] OTP_CTRL_ERR_CODE_3
    4'b 0001, // index[  9] OTP_CTRL_ERR_CODE_4
    4'b 0001, // index[ 10] OTP_CTRL_ERR_CODE_5
    4'b 0001, // index[ 11] OTP_CTRL_ERR_CODE_6
    4'b 0001, // index[ 12] OTP_CTRL_ERR_CODE_7
    4'b 0001, // index[ 13] OTP_CTRL_ERR_CODE_8
    4'b 0001, // index[ 14] OTP_CTRL_ERR_CODE_9
    4'b 0001, // index[ 15] OTP_CTRL_ERR_CODE_10
    4'b 0001, // index[ 16] OTP_CTRL_ERR_CODE_11
    4'b 0001, // index[ 17] OTP_CTRL_ERR_CODE_12
    4'b 0001, // index[ 18] OTP_CTRL_ERR_CODE_13
    4'b 0001, // index[ 19] OTP_CTRL_ERR_CODE_14
    4'b 0001, // index[ 20] OTP_CTRL_ERR_CODE_15
    4'b 0001, // index[ 21] OTP_CTRL_ERR_CODE_16
    4'b 0001, // index[ 22] OTP_CTRL_ERR_CODE_17
    4'b 0001, // index[ 23] OTP_CTRL_ERR_CODE_18
    4'b 0001, // index[ 24] OTP_CTRL_ERR_CODE_19
    4'b 0001, // index[ 25] OTP_CTRL_ERR_CODE_20
    4'b 0001, // index[ 26] OTP_CTRL_ERR_CODE_21
    4'b 0001, // index[ 27] OTP_CTRL_ERR_CODE_22
    4'b 0001, // index[ 28] OTP_CTRL_ERR_CODE_23
    4'b 0001, // index[ 29] OTP_CTRL_ERR_CODE_24
    4'b 0001, // index[ 30] OTP_CTRL_ERR_CODE_25
    4'b 0001, // index[ 31] OTP_CTRL_DIRECT_ACCESS_REGWEN
    4'b 0001, // index[ 32] OTP_CTRL_DIRECT_ACCESS_CMD
    4'b 0011, // index[ 33] OTP_CTRL_DIRECT_ACCESS_ADDRESS
    4'b 1111, // index[ 34] OTP_CTRL_DIRECT_ACCESS_WDATA_0
    4'b 1111, // index[ 35] OTP_CTRL_DIRECT_ACCESS_WDATA_1
    4'b 1111, // index[ 36] OTP_CTRL_DIRECT_ACCESS_RDATA_0
    4'b 1111, // index[ 37] OTP_CTRL_DIRECT_ACCESS_RDATA_1
    4'b 0001, // index[ 38] OTP_CTRL_CHECK_TRIGGER_REGWEN
    4'b 0001, // index[ 39] OTP_CTRL_CHECK_TRIGGER
    4'b 0001, // index[ 40] OTP_CTRL_CHECK_REGWEN
    4'b 1111, // index[ 41] OTP_CTRL_CHECK_TIMEOUT
    4'b 1111, // index[ 42] OTP_CTRL_INTEGRITY_CHECK_PERIOD
    4'b 1111, // index[ 43] OTP_CTRL_CONSISTENCY_CHECK_PERIOD
    4'b 0001, // index[ 44] OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK
    4'b 0001, // index[ 45] OTP_CTRL_SVN_PARTITION_READ_LOCK
    4'b 0001, // index[ 46] OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK
    4'b 0001, // index[ 47] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK
    4'b 0001, // index[ 48] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK
    4'b 0001, // index[ 49] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK
    4'b 0001, // index[ 50] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
    4'b 0001, // index[ 51] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_READ_LOCK
    4'b 0001, // index[ 52] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_READ_LOCK
    4'b 0001, // index[ 53] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_READ_LOCK
    4'b 0001, // index[ 54] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_READ_LOCK
    4'b 0001, // index[ 55] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_READ_LOCK
    4'b 0001, // index[ 56] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_READ_LOCK
    4'b 0001, // index[ 57] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_READ_LOCK
    4'b 0001, // index[ 58] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_READ_LOCK
    4'b 1111, // index[ 59] OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK
    4'b 1111, // index[ 60] OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK
    4'b 1111, // index[ 61] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0
    4'b 1111, // index[ 62] OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1
    4'b 1111, // index[ 63] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[ 64] OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[ 65] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0
    4'b 1111, // index[ 66] OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1
    4'b 1111, // index[ 67] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0
    4'b 1111, // index[ 68] OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1
    4'b 1111, // index[ 69] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0
    4'b 1111, // index[ 70] OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1
    4'b 1111, // index[ 71] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0
    4'b 1111, // index[ 72] OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1
    4'b 1111, // index[ 73] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[ 74] OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[ 75] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0
    4'b 1111, // index[ 76] OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1
    4'b 1111, // index[ 77] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0
    4'b 1111, // index[ 78] OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1
    4'b 1111, // index[ 79] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0
    4'b 1111, // index[ 80] OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1
    4'b 1111, // index[ 81] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[ 82] OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[ 83] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[ 84] OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[ 85] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[ 86] OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[ 87] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0
    4'b 1111, // index[ 88] OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1
    4'b 1111, // index[ 89] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0
    4'b 1111, // index[ 90] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1
    4'b 1111, // index[ 91] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0
    4'b 1111, // index[ 92] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1
    4'b 1111, // index[ 93] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0
    4'b 1111, // index[ 94] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1
    4'b 1111, // index[ 95] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0
    4'b 1111, // index[ 96] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1
    4'b 1111, // index[ 97] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0
    4'b 1111, // index[ 98] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1
    4'b 1111, // index[ 99] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0
    4'b 1111, // index[100] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1
    4'b 1111, // index[101] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0
    4'b 1111, // index[102] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1
    4'b 1111, // index[103] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0
    4'b 1111  // index[104] OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1
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
