#  NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
#  This is an automatically generated file by zahralak on Fri Apr 10 15:45:38 PDT 2026
# 
#  cmd:    veer -target=default -set=ret_stack_size=8 -set=btb_enable=1 -set=btb_fullya=0 -set=btb_size=512 -set=bht_size=512 -set=div_bit=4 -set=div_new=1 -set=dccm_enable=1 -set=dccm_num_banks=4 -set=dccm_region=0x3 -set=dccm_offset=0x00000 -set=dccm_size=16 -set=dma_buf_depth=5 -set=fast_interrupt_redirect=1 -set=icache_enable=1 -set=icache_waypack=1 -set=icache_ecc=1 -set=icache_size=16 -set=icache_2banks=1 -set=icache_num_ways=2 -set=icache_bypass_enable=1 -set=icache_num_bypass=2 -set=icache_num_tag_bypass=2 -set=icache_tag_bypass_enable=1 -set=iccm_enable=0 -set=iccm_num_banks=4 -set=iccm_region=0xC -set=iccm_offset=0x0 -set=iccm_size=128 -set=lsu_stbuf_depth=4 -set=lsu_num_nbload=4 -set=load_to_use_plus1=0 -set=pic_2cycle=0 -set=pic_region=0xB -set=pic_offset=0 -set=pic_size=32 -set=pic_total_int=255 -set=timer_legal_en=1 -set=bitmanip_zba=1 -set=bitmanip_zbb=1 -set=bitmanip_zbc=1 -set=bitmanip_zbe=0 -set=bitmanip_zbf=0 -set=bitmanip_zbp=0 -set=bitmanip_zbr=0 -set=bitmanip_zbs=1 -set=user_mode=1 -set=pmp_entries=64 -set=smepmp=1 -set=reset_vec=0x90000000 -fpga_optimize=0 -snapshot=nwp_config 
# 
# To use this in a perf script, use 'require $RV_ROOT/configs/config.pl'
# Reference the hash via $config{name}..


%config = (
            'reset_vec' => '0x90000000',
            'even_odd_trigger_chains' => 'true',
            'target' => 'default',
            'bus' => {
                       'ifu_bus_tag' => '3',
                       'lsu_bus_tag' => 3,
                       'sb_bus_id' => '1',
                       'ifu_bus_prty' => '2',
                       'ifu_bus_id' => '1',
                       'sb_bus_prty' => '2',
                       'lsu_bus_id' => '1',
                       'dma_bus_tag' => '1',
                       'lsu_bus_prty' => '2',
                       'bus_prty_default' => '3',
                       'sb_bus_tag' => '1',
                       'dma_bus_prty' => '2',
                       'dma_bus_id' => '1'
                     },
            'btb' => {
                       'btb_index1_lo' => '2',
                       'btb_index2_hi' => 17,
                       'btb_index3_hi' => 25,
                       'btb_addr_lo' => '2',
                       'btb_index3_lo' => 18,
                       'btb_enable' => '1',
                       'btb_index2_lo' => 10,
                       'btb_btag_size' => 5,
                       'btb_addr_hi' => 9,
                       'btb_index1_hi' => 9,
                       'btb_toffset_size' => '12',
                       'btb_btag_fold' => 0,
                       'btb_array_depth' => 256,
                       'btb_size' => 512,
                       'btb_fold2_index_hash' => 0
                     },
            'physical' => '1',
            'harts' => 1,
            'perf_events' => [
                               1,
                               2,
                               3,
                               4,
                               5,
                               6,
                               7,
                               8,
                               9,
                               10,
                               11,
                               12,
                               13,
                               14,
                               15,
                               16,
                               17,
                               18,
                               19,
                               20,
                               21,
                               22,
                               23,
                               24,
                               25,
                               26,
                               27,
                               28,
                               30,
                               31,
                               32,
                               34,
                               35,
                               36,
                               37,
                               38,
                               39,
                               40,
                               41,
                               42,
                               43,
                               44,
                               45,
                               46,
                               47,
                               48,
                               49,
                               50,
                               54,
                               55,
                               56,
                               512,
                               513,
                               514,
                               515,
                               516
                             ],
            'user_ec_rv_icg' => 'user_clock_gate',
            'pic' => {
                       'pic_meipt_count' => 255,
                       'pic_meipl_mask' => '0xf',
                       'pic_meip_mask' => '0x0',
                       'pic_meigwctrl_mask' => '0x3',
                       'pic_mpiccfg_count' => 1,
                       'pic_meipl_count' => 255,
                       'pic_offset' => '0',
                       'pic_meipt_offset' => '0x3004',
                       'pic_meigwclr_offset' => '0x5000',
                       'pic_mpiccfg_offset' => '0x3000',
                       'pic_bits' => 15,
                       'pic_meigwctrl_offset' => '0x4000',
                       'pic_meip_count' => 8,
                       'pic_total_int' => 255,
                       'pic_base_addr' => '0xb0000000',
                       'pic_int_words' => 8,
                       'pic_meie_count' => 255,
                       'pic_meie_mask' => '0x1',
                       'pic_meip_offset' => '0x1000',
                       'pic_meigwclr_count' => 255,
                       'pic_region' => '0xB',
                       'pic_size' => 32,
                       'pic_meie_offset' => '0x2000',
                       'pic_total_int_plus1' => 256,
                       'pic_meipt_mask' => '0x0',
                       'pic_meigwclr_mask' => '0x0',
                       'pic_mpiccfg_mask' => '0x1',
                       'pic_meipl_offset' => '0x0000',
                       'pic_meigwctrl_count' => 255
                     },
            'icache' => {
                          'icache_data_cell' => 'ram_512x71',
                          'icache_tag_num_bypass_width' => 2,
                          'icache_beat_bits' => 3,
                          'icache_size' => 16,
                          'icache_tag_lo' => 13,
                          'icache_bank_lo' => 3,
                          'icache_tag_num_bypass' => '2',
                          'icache_bank_width' => 8,
                          'icache_tag_index_lo' => '6',
                          'icache_data_width' => 64,
                          'icache_ecc' => '1',
                          'icache_fdata_width' => 71,
                          'icache_enable' => 1,
                          'icache_data_depth' => '512',
                          'icache_bypass_enable' => '1',
                          'icache_num_lines_bank' => '64',
                          'icache_index_hi' => 12,
                          'icache_data_index_lo' => 4,
                          'icache_bank_hi' => 3,
                          'icache_banks_way' => 2,
                          'icache_2banks' => '1',
                          'icache_num_lines_way' => '128',
                          'icache_tag_depth' => 128,
                          'icache_num_bypass' => '2',
                          'icache_beat_addr_hi' => 5,
                          'icache_scnd_last' => 6,
                          'icache_bank_bits' => 1,
                          'icache_ln_sz' => 64,
                          'icache_status_bits' => 1,
                          'icache_waypack' => '1',
                          'icache_tag_bypass_enable' => '1',
                          'icache_num_ways' => 2,
                          'icache_tag_cell' => 'ram_128x25',
                          'icache_num_beats' => 8,
                          'icache_num_bypass_width' => 2,
                          'icache_num_lines' => 256
                        },
            'tec_rv_icg' => 'clockhdr',
            'max_mmode_perf_event' => '516',
            'csr' => {
                       'mimpid' => {
                                     'reset' => '0x4',
                                     'mask' => '0x0',
                                     'exists' => 'true'
                                   },
                       'dicad0' => {
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'number' => '0x7c9',
                                     'mask' => '0xffffffff',
                                     'reset' => '0x0'
                                   },
                       'mcountinhibit' => {
                                            'commnet' => 'Performance counter inhibit. One bit per counter.',
                                            'mask' => '0x7d',
                                            'reset' => '0x0',
                                            'exists' => 'true',
                                            'poke_mask' => '0x7d'
                                          },
                       'mfdht' => {
                                    'exists' => 'true',
                                    'comment' => 'Force Debug Halt Threshold',
                                    'shared' => 'true',
                                    'reset' => '0x0',
                                    'mask' => '0x0000003f',
                                    'number' => '0x7ce'
                                  },
                       'meipt' => {
                                    'exists' => 'true',
                                    'comment' => 'External interrupt priority threshold.',
                                    'mask' => '0xf',
                                    'number' => '0xbc9',
                                    'reset' => '0x0'
                                  },
                       'mhpmcounter3' => {
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff',
                                           'exists' => 'true'
                                         },
                       'mitcnt0' => {
                                      'mask' => '0xffffffff',
                                      'number' => '0x7d2',
                                      'reset' => '0x0',
                                      'exists' => 'true'
                                    },
                       'meicidpl' => {
                                       'mask' => '0xf',
                                       'reset' => '0x0',
                                       'number' => '0xbcb',
                                       'exists' => 'true',
                                       'comment' => 'External interrupt claim id priority level.'
                                     },
                       'mhpmevent3' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'mitcnt1' => {
                                      'mask' => '0xffffffff',
                                      'number' => '0x7d5',
                                      'reset' => '0x0',
                                      'exists' => 'true'
                                    },
                       'dcsr' => {
                                   'reset' => '0x40000003',
                                   'mask' => '0x00008c04',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'poke_mask' => '0x00008dcc'
                                 },
                       'meicurpl' => {
                                       'comment' => 'External interrupt current priority level.',
                                       'exists' => 'true',
                                       'reset' => '0x0',
                                       'mask' => '0xf',
                                       'number' => '0xbcc'
                                     },
                       'mcgc' => {
                                   'poke_mask' => '0x000003ff',
                                   'exists' => 'true',
                                   'mask' => '0x000003ff',
                                   'reset' => '0x200',
                                   'number' => '0x7f8'
                                 },
                       'mitbnd0' => {
                                      'exists' => 'true',
                                      'mask' => '0xffffffff',
                                      'number' => '0x7d3',
                                      'reset' => '0xffffffff'
                                    },
                       'dmst' => {
                                   'mask' => '0x0',
                                   'reset' => '0x0',
                                   'number' => '0x7c4',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'comment' => 'Memory synch trigger: Flush caches in debug mode.'
                                 },
                       'mhpmcounter6h' => {
                                            'exists' => 'true',
                                            'mask' => '0xffffffff',
                                            'reset' => '0x0'
                                          },
                       'mie' => {
                                  'exists' => 'true',
                                  'reset' => '0x0',
                                  'mask' => '0x70000888'
                                },
                       'cycle' => {
                                    'exists' => 'false'
                                  },
                       'mhpmcounter4' => {
                                           'exists' => 'true',
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff'
                                         },
                       'mhpmevent5' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'mrac' => {
                                   'shared' => 'true',
                                   'number' => '0x7c0',
                                   'mask' => '0xffffffff',
                                   'reset' => '0x0',
                                   'comment' => 'Memory region io and cache control.',
                                   'exists' => 'true'
                                 },
                       'mdccmect' => {
                                       'exists' => 'true',
                                       'reset' => '0x0',
                                       'mask' => '0xffffffff',
                                       'number' => '0x7f2'
                                     },
                       'mhpmcounter5h' => {
                                            'exists' => 'true',
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff'
                                          },
                       'tselect' => {
                                      'reset' => '0x0',
                                      'mask' => '0x3',
                                      'exists' => 'true'
                                    },
                       'mhpmcounter4h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'mhartid' => {
                                      'exists' => 'true',
                                      'poke_mask' => '0xfffffff0',
                                      'mask' => '0x0',
                                      'reset' => '0x0'
                                    },
                       'mcpc' => {
                                   'reset' => '0x0',
                                   'mask' => '0x0',
                                   'number' => '0x7c2',
                                   'comment' => 'Core pause',
                                   'exists' => 'true'
                                 },
                       'instret' => {
                                      'exists' => 'false'
                                    },
                       'mitctl0' => {
                                      'exists' => 'true',
                                      'mask' => '0x00000007',
                                      'number' => '0x7d4',
                                      'reset' => '0x1'
                                    },
                       'mhpmcounter6' => {
                                           'exists' => 'true',
                                           'mask' => '0xffffffff',
                                           'reset' => '0x0'
                                         },
                       'micect' => {
                                     'reset' => '0x0',
                                     'mask' => '0xffffffff',
                                     'number' => '0x7f0',
                                     'exists' => 'true'
                                   },
                       'mhpmcounter3h' => {
                                            'mask' => '0xffffffff',
                                            'reset' => '0x0',
                                            'exists' => 'true'
                                          },
                       'mhpmcounter5' => {
                                           'exists' => 'true',
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff'
                                         },
                       'mcounteren' => {
                                         'exists' => 'false'
                                       },
                       'dicad1' => {
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'debug' => 'true',
                                     'mask' => '0x3',
                                     'reset' => '0x0',
                                     'number' => '0x7ca'
                                   },
                       'mitbnd1' => {
                                      'reset' => '0xffffffff',
                                      'mask' => '0xffffffff',
                                      'number' => '0x7d6',
                                      'exists' => 'true'
                                    },
                       'mitctl1' => {
                                      'mask' => '0x0000000f',
                                      'reset' => '0x1',
                                      'number' => '0x7d7',
                                      'exists' => 'true'
                                    },
                       'mscause' => {
                                      'exists' => 'true',
                                      'mask' => '0x0000000f',
                                      'number' => '0x7ff',
                                      'reset' => '0x0'
                                    },
                       'mhpmevent4' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'misa' => {
                                   'reset' => '0x40001104',
                                   'mask' => '0x0',
                                   'exists' => 'true'
                                 },
                       'dicawics' => {
                                       'reset' => '0x0',
                                       'mask' => '0x0130fffc',
                                       'number' => '0x7c8',
                                       'comment' => 'Cache diagnostics.',
                                       'exists' => 'true',
                                       'debug' => 'true'
                                     },
                       'marchid' => {
                                      'exists' => 'true',
                                      'reset' => '0x00000010',
                                      'mask' => '0x0'
                                    },
                       'mfdc' => {
                                   'exists' => 'true',
                                   'mask' => '0x00071fff',
                                   'reset' => '0x00070040',
                                   'number' => '0x7f9'
                                 },
                       'mfdhs' => {
                                    'reset' => '0x0',
                                    'mask' => '0x00000003',
                                    'number' => '0x7cf',
                                    'comment' => 'Force Debug Halt Status',
                                    'exists' => 'true'
                                  },
                       'dicago' => {
                                     'reset' => '0x0',
                                     'mask' => '0x0',
                                     'number' => '0x7cb',
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'debug' => 'true'
                                   },
                       'mip' => {
                                  'exists' => 'true',
                                  'poke_mask' => '0x70000888',
                                  'mask' => '0x0',
                                  'reset' => '0x0'
                                },
                       'mstatus' => {
                                      'exists' => 'true',
                                      'reset' => '0x1800',
                                      'mask' => '0x88'
                                    },
                       'miccmect' => {
                                       'mask' => '0xffffffff',
                                       'reset' => '0x0',
                                       'number' => '0x7f1',
                                       'exists' => 'true'
                                     },
                       'time' => {
                                   'exists' => 'false'
                                 },
                       'mhpmevent6' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'mpmc' => {
                                   'exists' => 'true',
                                   'reset' => '0x2',
                                   'mask' => '0x2',
                                   'number' => '0x7c6'
                                 },
                       'mvendorid' => {
                                        'reset' => '0x45',
                                        'mask' => '0x0',
                                        'exists' => 'true'
                                      }
                     },
            'protection' => {
                              'data_access_addr6' => '0x00000000',
                              'inst_access_addr3' => '0x00000000',
                              'inst_access_mask2' => '0xffffffff',
                              'data_access_enable4' => '0x0',
                              'data_access_addr3' => '0x00000000',
                              'data_access_enable1' => '0x0',
                              'data_access_enable7' => '0x0',
                              'inst_access_enable4' => '0x0',
                              'inst_access_enable6' => '0x0',
                              'inst_access_enable0' => '0x0',
                              'data_access_mask0' => '0xffffffff',
                              'data_access_mask7' => '0xffffffff',
                              'inst_access_enable5' => '0x0',
                              'data_access_mask4' => '0xffffffff',
                              'inst_access_addr5' => '0x00000000',
                              'data_access_enable6' => '0x0',
                              'data_access_mask5' => '0xffffffff',
                              'data_access_addr5' => '0x00000000',
                              'inst_access_addr4' => '0x00000000',
                              'data_access_addr0' => '0x00000000',
                              'data_access_enable0' => '0x0',
                              'data_access_mask6' => '0xffffffff',
                              'data_access_enable3' => '0x0',
                              'inst_access_addr0' => '0x00000000',
                              'data_access_mask1' => '0xffffffff',
                              'inst_access_enable2' => '0x0',
                              'inst_access_mask5' => '0xffffffff',
                              'pmp_entries' => '64',
                              'data_access_mask3' => '0xffffffff',
                              'inst_access_mask7' => '0xffffffff',
                              'inst_access_addr2' => '0x00000000',
                              'inst_access_mask1' => '0xffffffff',
                              'smepmp' => '1',
                              'data_access_addr2' => '0x00000000',
                              'inst_access_mask4' => '0xffffffff',
                              'inst_access_addr7' => '0x00000000',
                              'data_access_addr4' => '0x00000000',
                              'data_access_addr1' => '0x00000000',
                              'data_access_enable5' => '0x0',
                              'data_access_addr7' => '0x00000000',
                              'data_access_enable2' => '0x0',
                              'inst_access_enable7' => '0x0',
                              'inst_access_mask3' => '0xffffffff',
                              'inst_access_enable3' => '0x0',
                              'inst_access_mask6' => '0xffffffff',
                              'inst_access_mask0' => '0xffffffff',
                              'data_access_mask2' => '0xffffffff',
                              'inst_access_addr1' => '0x00000000',
                              'inst_access_addr6' => '0x00000000',
                              'inst_access_enable1' => '0x0'
                            },
            'core' => {
                        'bitmanip_zba' => 1,
                        'dma_buf_depth' => '5',
                        'icache_only' => 1,
                        'iccm_only' => 'derived',
                        'lsu_stbuf_depth' => '4',
                        'user_mode' => '1',
                        'div_bit' => '4',
                        'fast_interrupt_redirect' => '1',
                        'no_iccm_no_icache' => 'derived',
                        'bitmanip_zbp' => 0,
                        'iccm_icache' => 'derived',
                        'bitmanip_zbe' => 0,
                        'lsu2dma' => 0,
                        'bitmanip_zbr' => 0,
                        'timer_legal_en' => '1',
                        'lsu_num_nbload_width' => '2',
                        'bitmanip_zbs' => 1,
                        'bitmanip_zbf' => 0,
                        'bitmanip_zbc' => 1,
                        'bitmanip_zbb' => 1,
                        'lsu_num_nbload' => '4',
                        'div_new' => 1
                      },
            'config_key' => '32\'hdeadbeef',
            'nmi_vec' => '0x11110000',
            'regwidth' => '32',
            'triggers' => [
                            {
                              'poke_mask' => [
                                               '0x081818c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ]
                            },
                            {
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ]
                            },
                            {
                              'poke_mask' => [
                                               '0x081818c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ]
                            },
                            {
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ]
                            }
                          ],
            'num_mmode_perf_regs' => '4',
            'numiregs' => '32',
            'memmap' => {
                          'unused_region6' => '0x10000000',
                          'unused_region1' => '0x70000000',
                          'external_data' => '0xe0580000',
                          'unused_region0' => '0x80000000',
                          'unused_region3' => '0x50000000',
                          'unused_region7' => '0x00000000',
                          'debug_sb_mem' => '0xa0580000',
                          'unused_region4' => '0x40000000',
                          'consoleio' => '0xf0580000',
                          'unused_region2' => '0x60000000',
                          'serialio' => '0xf0580000',
                          'unused_region5' => '0x20000000',
                          'external_data_1' => '0xd0000000'
                        },
            'testbench' => {
                             'RV_TOP' => '`TOP.rvtop_wrapper.rvtop',
                             'TOP' => 'tb_top',
                             'clock_period' => '100',
                             'build_axi_native' => 1,
                             'build_axi4' => 1,
                             'lderr_rollback' => '1',
                             'ext_addrwidth' => '32',
                             'ext_datawidth' => '64',
                             'SDVT_AHB' => '0',
                             'sterr_rollback' => '0',
                             'CPU_TOP' => '`RV_TOP.veer'
                           },
            'iccm' => {
                        'iccm_bank_bits' => 2,
                        'iccm_bits' => 17,
                        'iccm_num_banks_4' => '',
                        'iccm_bank_hi' => 3,
                        'iccm_eadr' => '0xc001ffff',
                        'iccm_offset' => '0x0',
                        'iccm_region' => '0xC',
                        'iccm_sadr' => '0xc0000000',
                        'iccm_rows' => '8192',
                        'iccm_ecc_width' => '7',
                        'iccm_num_banks' => '4',
                        'iccm_bank_index_lo' => 4,
                        'iccm_size' => 128,
                        'iccm_size_128' => '',
                        'iccm_index_bits' => 13,
                        'iccm_reserved' => '0x1000',
                        'iccm_data_cell' => 'ram_8192x39'
                      },
            'bht' => {
                       'bht_ghr_hash_1' => '',
                       'bht_hash_string' => '{hashin[8+1:2]^ghr[8-1:0]}// cf2',
                       'bht_addr_hi' => 9,
                       'bht_ghr_size' => 8,
                       'bht_addr_lo' => '2',
                       'bht_array_depth' => 256,
                       'bht_size' => 512,
                       'bht_ghr_range' => '7:0'
                     },
            'dccm' => {
                        'dccm_data_cell' => 'ram_1024x39',
                        'dccm_bank_bits' => 2,
                        'dccm_bits' => 14,
                        'dccm_index_bits' => 10,
                        'dccm_size' => 16,
                        'dccm_data_width' => 32,
                        'dccm_sadr' => '0x30000000',
                        'dccm_size_16' => '',
                        'dccm_ecc_width' => 7,
                        'lsu_sb_bits' => 14,
                        'dccm_rows' => '1024',
                        'dccm_fdata_width' => 39,
                        'dccm_byte_width' => '4',
                        'dccm_reserved' => '0x1400',
                        'dccm_eadr' => '0x30003fff',
                        'dccm_region' => '0x3',
                        'dccm_num_banks' => '4',
                        'dccm_offset' => '0x00000',
                        'dccm_width_bits' => 2,
                        'dccm_num_banks_4' => '',
                        'dccm_enable' => '1'
                      },
            'xlen' => 32,
            'retstack' => {
                            'ret_stack_size' => '8'
                          }
          );
1;
