#  NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
#  This is an automatically generated file by cwhitehead on Thu Oct  9 09:50:20 PDT 2025
# 
#  cmd:    veer -target=default -set=ret_stack_size=8 -set=btb_enable=1 -set=btb_fullya=0 -set=btb_size=512 -set=bht_size=512 -set=div_bit=4 -set=div_new=1 -set=dccm_enable=1 -set=dccm_num_banks=4 -set=dccm_region=0x5 -set=dccm_offset=0x00000 -set=dccm_size=16 -set=dma_buf_depth=5 -set=fast_interrupt_redirect=1 -set=icache_enable=1 -set=icache_waypack=1 -set=icache_ecc=1 -set=icache_size=16 -set=icache_2banks=1 -set=icache_num_ways=2 -set=icache_bypass_enable=1 -set=icache_num_bypass=2 -set=icache_num_tag_bypass=2 -set=icache_tag_bypass_enable=1 -set=iccm_enable=0 -set=iccm_num_banks=4 -set=iccm_region=0x4 -set=iccm_offset=0x0 -set=iccm_size=128 -set=lsu_stbuf_depth=4 -set=lsu_num_nbload=4 -set=load_to_use_plus1=0 -set=pic_2cycle=0 -set=pic_region=0x6 -set=pic_offset=0 -set=pic_size=32 -set=pic_total_int=255 -set=timer_legal_en=1 -set=bitmanip_zba=1 -set=bitmanip_zbb=1 -set=bitmanip_zbc=1 -set=bitmanip_zbe=0 -set=bitmanip_zbf=0 -set=bitmanip_zbp=0 -set=bitmanip_zbr=0 -set=bitmanip_zbs=1 -set=user_mode=1 -set=pmp_entries=64 -set=smepmp=1 -set=reset_vec=0x80000000 -fpga_optimize=0 -snapshot=20251009_ahb_lint_fix_css 
# 
# To use this in a perf script, use 'require $RV_ROOT/configs/config.pl'
# Reference the hash via $config{name}..


%config = (
            'protection' => {
                              'inst_access_addr0' => '0x00000000',
                              'inst_access_mask7' => '0xffffffff',
                              'data_access_addr6' => '0x00000000',
                              'inst_access_enable1' => '0x0',
                              'data_access_mask4' => '0xffffffff',
                              'data_access_enable5' => '0x0',
                              'data_access_mask2' => '0xffffffff',
                              'data_access_addr2' => '0x00000000',
                              'data_access_enable6' => '0x0',
                              'data_access_addr4' => '0x00000000',
                              'data_access_mask6' => '0xffffffff',
                              'inst_access_mask0' => '0xffffffff',
                              'inst_access_addr7' => '0x00000000',
                              'data_access_enable4' => '0x0',
                              'inst_access_mask5' => '0xffffffff',
                              'inst_access_enable2' => '0x0',
                              'inst_access_addr3' => '0x00000000',
                              'data_access_enable3' => '0x0',
                              'inst_access_enable7' => '0x0',
                              'data_access_addr1' => '0x00000000',
                              'data_access_mask1' => '0xffffffff',
                              'inst_access_mask3' => '0xffffffff',
                              'inst_access_addr5' => '0x00000000',
                              'inst_access_enable0' => '0x0',
                              'data_access_addr5' => '0x00000000',
                              'data_access_enable0' => '0x0',
                              'data_access_mask3' => '0xffffffff',
                              'inst_access_mask1' => '0xffffffff',
                              'inst_access_addr1' => '0x00000000',
                              'data_access_enable7' => '0x0',
                              'data_access_addr3' => '0x00000000',
                              'inst_access_enable3' => '0x0',
                              'data_access_mask5' => '0xffffffff',
                              'smepmp' => '1',
                              'data_access_enable2' => '0x0',
                              'data_access_mask0' => '0xffffffff',
                              'data_access_addr7' => '0x00000000',
                              'inst_access_enable4' => '0x0',
                              'inst_access_mask6' => '0xffffffff',
                              'inst_access_enable6' => '0x0',
                              'inst_access_addr4' => '0x00000000',
                              'inst_access_addr2' => '0x00000000',
                              'inst_access_enable5' => '0x0',
                              'inst_access_mask2' => '0xffffffff',
                              'inst_access_mask4' => '0xffffffff',
                              'inst_access_addr6' => '0x00000000',
                              'data_access_enable1' => '0x0',
                              'data_access_addr0' => '0x00000000',
                              'pmp_entries' => '64',
                              'data_access_mask7' => '0xffffffff'
                            },
            'pic' => {
                       'pic_meipl_count' => 255,
                       'pic_total_int_plus1' => 256,
                       'pic_meip_mask' => '0x0',
                       'pic_meigwclr_count' => 255,
                       'pic_meipl_offset' => '0x0000',
                       'pic_offset' => '0',
                       'pic_meigwclr_mask' => '0x0',
                       'pic_meipt_count' => 255,
                       'pic_meigwctrl_mask' => '0x3',
                       'pic_meie_offset' => '0x2000',
                       'pic_base_addr' => '0x60000000',
                       'pic_meip_count' => 8,
                       'pic_meigwctrl_count' => 255,
                       'pic_region' => '0x6',
                       'pic_meipt_offset' => '0x3004',
                       'pic_int_words' => 8,
                       'pic_mpiccfg_offset' => '0x3000',
                       'pic_mpiccfg_count' => 1,
                       'pic_meipt_mask' => '0x0',
                       'pic_meie_mask' => '0x1',
                       'pic_size' => 32,
                       'pic_total_int' => 255,
                       'pic_bits' => 15,
                       'pic_mpiccfg_mask' => '0x1',
                       'pic_meipl_mask' => '0xf',
                       'pic_meigwclr_offset' => '0x5000',
                       'pic_meip_offset' => '0x1000',
                       'pic_meie_count' => 255,
                       'pic_meigwctrl_offset' => '0x4000'
                     },
            'harts' => 1,
            'config_key' => '32\'hdeadbeef',
            'triggers' => [
                            {
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'poke_mask' => [
                                               '0x081818c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ]
                            },
                            {
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ]
                            },
                            {
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'poke_mask' => [
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
            'tec_rv_icg' => 'clockhdr',
            'bht' => {
                       'bht_addr_lo' => '2',
                       'bht_ghr_hash_1' => '',
                       'bht_ghr_size' => 8,
                       'bht_array_depth' => 256,
                       'bht_size' => 512,
                       'bht_hash_string' => '{hashin[8+1:2]^ghr[8-1:0]}// cf2',
                       'bht_addr_hi' => 9,
                       'bht_ghr_range' => '7:0'
                     },
            'csr' => {
                       'mrac' => {
                                   'reset' => '0x0',
                                   'shared' => 'true',
                                   'number' => '0x7c0',
                                   'exists' => 'true',
                                   'mask' => '0xffffffff',
                                   'comment' => 'Memory region io and cache control.'
                                 },
                       'mfdc' => {
                                   'number' => '0x7f9',
                                   'exists' => 'true',
                                   'mask' => '0x00071fff',
                                   'reset' => '0x00070040'
                                 },
                       'miccmect' => {
                                       'exists' => 'true',
                                       'number' => '0x7f1',
                                       'mask' => '0xffffffff',
                                       'reset' => '0x0'
                                     },
                       'mhpmcounter5h' => {
                                            'mask' => '0xffffffff',
                                            'exists' => 'true',
                                            'reset' => '0x0'
                                          },
                       'mip' => {
                                  'mask' => '0x0',
                                  'exists' => 'true',
                                  'poke_mask' => '0x70000888',
                                  'reset' => '0x0'
                                },
                       'mdccmect' => {
                                       'reset' => '0x0',
                                       'number' => '0x7f2',
                                       'exists' => 'true',
                                       'mask' => '0xffffffff'
                                     },
                       'micect' => {
                                     'reset' => '0x0',
                                     'exists' => 'true',
                                     'number' => '0x7f0',
                                     'mask' => '0xffffffff'
                                   },
                       'mhpmevent6' => {
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff',
                                         'exists' => 'true'
                                       },
                       'mfdhs' => {
                                    'exists' => 'true',
                                    'mask' => '0x00000003',
                                    'number' => '0x7cf',
                                    'comment' => 'Force Debug Halt Status',
                                    'reset' => '0x0'
                                  },
                       'mitbnd0' => {
                                      'number' => '0x7d3',
                                      'exists' => 'true',
                                      'mask' => '0xffffffff',
                                      'reset' => '0xffffffff'
                                    },
                       'dcsr' => {
                                   'mask' => '0x00008c04',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'reset' => '0x40000003',
                                   'poke_mask' => '0x00008dcc'
                                 },
                       'mhpmcounter4h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'marchid' => {
                                      'exists' => 'true',
                                      'mask' => '0x0',
                                      'reset' => '0x00000010'
                                    },
                       'tselect' => {
                                      'exists' => 'true',
                                      'mask' => '0x3',
                                      'reset' => '0x0'
                                    },
                       'mhpmcounter6' => {
                                           'mask' => '0xffffffff',
                                           'exists' => 'true',
                                           'reset' => '0x0'
                                         },
                       'mcounteren' => {
                                         'exists' => 'false'
                                       },
                       'mimpid' => {
                                     'exists' => 'true',
                                     'mask' => '0x0',
                                     'reset' => '0x4'
                                   },
                       'mitcnt1' => {
                                      'exists' => 'true',
                                      'number' => '0x7d5',
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0'
                                    },
                       'meicurpl' => {
                                       'reset' => '0x0',
                                       'comment' => 'External interrupt current priority level.',
                                       'exists' => 'true',
                                       'number' => '0xbcc',
                                       'mask' => '0xf'
                                     },
                       'mitctl1' => {
                                      'exists' => 'true',
                                      'mask' => '0x0000000f',
                                      'number' => '0x7d7',
                                      'reset' => '0x1'
                                    },
                       'dicad1' => {
                                     'reset' => '0x0',
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'number' => '0x7ca',
                                     'mask' => '0x3'
                                   },
                       'mhpmcounter3h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'mvendorid' => {
                                        'mask' => '0x0',
                                        'exists' => 'true',
                                        'reset' => '0x45'
                                      },
                       'instret' => {
                                      'exists' => 'false'
                                    },
                       'mhpmevent5' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'meipt' => {
                                    'comment' => 'External interrupt priority threshold.',
                                    'exists' => 'true',
                                    'mask' => '0xf',
                                    'number' => '0xbc9',
                                    'reset' => '0x0'
                                  },
                       'mfdht' => {
                                    'reset' => '0x0',
                                    'shared' => 'true',
                                    'exists' => 'true',
                                    'number' => '0x7ce',
                                    'mask' => '0x0000003f',
                                    'comment' => 'Force Debug Halt Threshold'
                                  },
                       'mie' => {
                                  'reset' => '0x0',
                                  'mask' => '0x70000888',
                                  'exists' => 'true'
                                },
                       'dicawics' => {
                                       'number' => '0x7c8',
                                       'mask' => '0x0130fffc',
                                       'exists' => 'true',
                                       'debug' => 'true',
                                       'comment' => 'Cache diagnostics.',
                                       'reset' => '0x0'
                                     },
                       'cycle' => {
                                    'exists' => 'false'
                                  },
                       'mcountinhibit' => {
                                            'exists' => 'true',
                                            'mask' => '0x7d',
                                            'commnet' => 'Performance counter inhibit. One bit per counter.',
                                            'poke_mask' => '0x7d',
                                            'reset' => '0x0'
                                          },
                       'dmst' => {
                                   'reset' => '0x0',
                                   'comment' => 'Memory synch trigger: Flush caches in debug mode.',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'mask' => '0x0',
                                   'number' => '0x7c4'
                                 },
                       'mhpmevent3' => {
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff',
                                         'exists' => 'true'
                                       },
                       'mhpmevent4' => {
                                         'exists' => 'true',
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0'
                                       },
                       'time' => {
                                   'exists' => 'false'
                                 },
                       'mhpmcounter4' => {
                                           'exists' => 'true',
                                           'mask' => '0xffffffff',
                                           'reset' => '0x0'
                                         },
                       'mcgc' => {
                                   'poke_mask' => '0x000003ff',
                                   'reset' => '0x200',
                                   'exists' => 'true',
                                   'mask' => '0x000003ff',
                                   'number' => '0x7f8'
                                 },
                       'mpmc' => {
                                   'exists' => 'true',
                                   'number' => '0x7c6',
                                   'mask' => '0x2',
                                   'reset' => '0x2'
                                 },
                       'mhpmcounter6h' => {
                                            'mask' => '0xffffffff',
                                            'exists' => 'true',
                                            'reset' => '0x0'
                                          },
                       'mitbnd1' => {
                                      'reset' => '0xffffffff',
                                      'exists' => 'true',
                                      'number' => '0x7d6',
                                      'mask' => '0xffffffff'
                                    },
                       'mhartid' => {
                                      'reset' => '0x0',
                                      'poke_mask' => '0xfffffff0',
                                      'exists' => 'true',
                                      'mask' => '0x0'
                                    },
                       'dicago' => {
                                     'number' => '0x7cb',
                                     'exists' => 'true',
                                     'mask' => '0x0',
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'reset' => '0x0'
                                   },
                       'mhpmcounter5' => {
                                           'reset' => '0x0',
                                           'exists' => 'true',
                                           'mask' => '0xffffffff'
                                         },
                       'mscause' => {
                                      'number' => '0x7ff',
                                      'exists' => 'true',
                                      'mask' => '0x0000000f',
                                      'reset' => '0x0'
                                    },
                       'misa' => {
                                   'reset' => '0x40001104',
                                   'exists' => 'true',
                                   'mask' => '0x0'
                                 },
                       'mitctl0' => {
                                      'exists' => 'true',
                                      'mask' => '0x00000007',
                                      'number' => '0x7d4',
                                      'reset' => '0x1'
                                    },
                       'mitcnt0' => {
                                      'exists' => 'true',
                                      'number' => '0x7d2',
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0'
                                    },
                       'meicidpl' => {
                                       'comment' => 'External interrupt claim id priority level.',
                                       'exists' => 'true',
                                       'mask' => '0xf',
                                       'number' => '0xbcb',
                                       'reset' => '0x0'
                                     },
                       'mcpc' => {
                                   'reset' => '0x0',
                                   'comment' => 'Core pause',
                                   'exists' => 'true',
                                   'mask' => '0x0',
                                   'number' => '0x7c2'
                                 },
                       'mstatus' => {
                                      'reset' => '0x1800',
                                      'mask' => '0x88',
                                      'exists' => 'true'
                                    },
                       'mhpmcounter3' => {
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff',
                                           'exists' => 'true'
                                         },
                       'dicad0' => {
                                     'exists' => 'true',
                                     'number' => '0x7c9',
                                     'mask' => '0xffffffff',
                                     'reset' => '0x0',
                                     'comment' => 'Cache diagnostics.',
                                     'debug' => 'true'
                                   }
                     },
            'icache' => {
                          'icache_num_bypass_width' => 2,
                          'icache_num_ways' => 2,
                          'icache_num_lines' => 256,
                          'icache_num_lines_bank' => '64',
                          'icache_bypass_enable' => '1',
                          'icache_bank_hi' => 3,
                          'icache_bank_lo' => 3,
                          'icache_index_hi' => 12,
                          'icache_data_index_lo' => 4,
                          'icache_num_beats' => 8,
                          'icache_tag_num_bypass_width' => 2,
                          'icache_bank_width' => 8,
                          'icache_status_bits' => 1,
                          'icache_data_width' => 64,
                          'icache_enable' => 1,
                          'icache_banks_way' => 2,
                          'icache_beat_addr_hi' => 5,
                          'icache_2banks' => '1',
                          'icache_ln_sz' => 64,
                          'icache_data_cell' => 'ram_512x71',
                          'icache_scnd_last' => 6,
                          'icache_tag_depth' => 128,
                          'icache_data_depth' => '512',
                          'icache_num_lines_way' => '128',
                          'icache_tag_bypass_enable' => '1',
                          'icache_tag_index_lo' => '6',
                          'icache_bank_bits' => 1,
                          'icache_tag_num_bypass' => '2',
                          'icache_beat_bits' => 3,
                          'icache_waypack' => '1',
                          'icache_fdata_width' => 71,
                          'icache_size' => 16,
                          'icache_num_bypass' => '2',
                          'icache_ecc' => '1',
                          'icache_tag_cell' => 'ram_128x25',
                          'icache_tag_lo' => 13
                        },
            'dccm' => {
                        'dccm_index_bits' => 10,
                        'dccm_data_cell' => 'ram_1024x39',
                        'dccm_region' => '0x5',
                        'dccm_rows' => '1024',
                        'dccm_data_width' => 32,
                        'dccm_enable' => '1',
                        'dccm_num_banks_4' => '',
                        'dccm_size' => 16,
                        'dccm_size_16' => '',
                        'dccm_width_bits' => 2,
                        'lsu_sb_bits' => 14,
                        'dccm_num_banks' => '4',
                        'dccm_eadr' => '0x50003fff',
                        'dccm_byte_width' => '4',
                        'dccm_bits' => 14,
                        'dccm_offset' => '0x00000',
                        'dccm_ecc_width' => 7,
                        'dccm_reserved' => '0x1400',
                        'dccm_fdata_width' => 39,
                        'dccm_bank_bits' => 2,
                        'dccm_sadr' => '0x50000000'
                      },
            'iccm' => {
                        'iccm_index_bits' => 13,
                        'iccm_data_cell' => 'ram_8192x39',
                        'iccm_region' => '0x4',
                        'iccm_rows' => '8192',
                        'iccm_num_banks_4' => '',
                        'iccm_size' => 128,
                        'iccm_num_banks' => '4',
                        'iccm_bank_hi' => 3,
                        'iccm_eadr' => '0x4001ffff',
                        'iccm_offset' => '0x0',
                        'iccm_bits' => 17,
                        'iccm_bank_index_lo' => 4,
                        'iccm_size_128' => '',
                        'iccm_ecc_width' => '7',
                        'iccm_reserved' => '0x1000',
                        'iccm_bank_bits' => 2,
                        'iccm_sadr' => '0x40000000'
                      },
            'max_mmode_perf_event' => '516',
            'numiregs' => '32',
            'testbench' => {
                             'SDVT_AHB' => '0',
                             'CPU_TOP' => '`RV_TOP.veer',
                             'lderr_rollback' => '1',
                             'ext_datawidth' => '64',
                             'RV_TOP' => '`TOP.rvtop_wrapper.rvtop',
                             'TOP' => 'tb_top',
                             'sterr_rollback' => '0',
                             'build_axi4' => 1,
                             'ext_addrwidth' => '32',
                             'build_axi_native' => 1,
                             'clock_period' => '100'
                           },
            'nmi_vec' => '0x11110000',
            'regwidth' => '32',
            'physical' => '1',
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
            'bus' => {
                       'sb_bus_id' => '1',
                       'ifu_bus_tag' => '3',
                       'sb_bus_prty' => '2',
                       'dma_bus_tag' => '1',
                       'dma_bus_prty' => '2',
                       'bus_prty_default' => '3',
                       'ifu_bus_id' => '1',
                       'dma_bus_id' => '1',
                       'sb_bus_tag' => '1',
                       'ifu_bus_prty' => '2',
                       'lsu_bus_id' => '1',
                       'lsu_bus_prty' => '2',
                       'lsu_bus_tag' => 3
                     },
            'target' => 'default',
            'num_mmode_perf_regs' => '4',
            'reset_vec' => '0x80000000',
            'even_odd_trigger_chains' => 'true',
            'xlen' => 32,
            'retstack' => {
                            'ret_stack_size' => '8'
                          },
            'core' => {
                        'lsu_stbuf_depth' => '4',
                        'bitmanip_zbf' => 0,
                        'user_mode' => '1',
                        'bitmanip_zbp' => 0,
                        'lsu_num_nbload_width' => '2',
                        'icache_only' => 1,
                        'iccm_icache' => 'derived',
                        'dma_buf_depth' => '5',
                        'bitmanip_zbc' => 1,
                        'fast_interrupt_redirect' => '1',
                        'div_new' => 1,
                        'lsu2dma' => 0,
                        'bitmanip_zbe' => 0,
                        'bitmanip_zbs' => 1,
                        'bitmanip_zba' => 1,
                        'iccm_only' => 'derived',
                        'bitmanip_zbb' => 1,
                        'timer_legal_en' => '1',
                        'bitmanip_zbr' => 0,
                        'div_bit' => '4',
                        'no_iccm_no_icache' => 'derived',
                        'lsu_num_nbload' => '4'
                      },
            'memmap' => {
                          'consoleio' => '0xf0580000',
                          'debug_sb_mem' => '0xc0580000',
                          'unused_region5' => '0x20000000',
                          'unused_region4' => '0x30000000',
                          'external_data_1' => '0xd0000000',
                          'unused_region2' => '0x90000000',
                          'unused_region1' => '0xa0000000',
                          'unused_region6' => '0x10000000',
                          'unused_region0' => '0xb0000000',
                          'unused_region3' => '0x70000000',
                          'serialio' => '0xf0580000',
                          'unused_region7' => '0x00000000',
                          'external_data' => '0xe0580000'
                        },
            'user_ec_rv_icg' => 'user_clock_gate',
            'btb' => {
                       'btb_toffset_size' => '12',
                       'btb_index2_hi' => 17,
                       'btb_array_depth' => 256,
                       'btb_index1_lo' => '2',
                       'btb_index3_lo' => 18,
                       'btb_size' => 512,
                       'btb_fold2_index_hash' => 0,
                       'btb_btag_fold' => 0,
                       'btb_index2_lo' => 10,
                       'btb_addr_lo' => '2',
                       'btb_btag_size' => 5,
                       'btb_index3_hi' => 25,
                       'btb_index1_hi' => 9,
                       'btb_enable' => '1',
                       'btb_addr_hi' => 9
                     }
          );
1;
