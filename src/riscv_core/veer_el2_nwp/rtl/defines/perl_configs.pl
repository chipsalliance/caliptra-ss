#  NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
#  This is an automatically generated file by zahralak on Mon Apr 27 16:02:14 PDT 2026
# 
#  cmd:    veer -target=default -set=ret_stack_size=8 -set=btb_enable=1 -set=btb_fullya=0 -set=btb_size=512 -set=bht_size=512 -set=div_bit=4 -set=div_new=1 -set=dccm_enable=1 -set=dccm_num_banks=4 -set=dccm_region=0x3 -set=dccm_offset=0x00000 -set=dccm_size=64 -set=dma_buf_depth=5 -set=fast_interrupt_redirect=1 -set=icache_enable=1 -set=icache_waypack=1 -set=icache_ecc=1 -set=icache_size=16 -set=icache_2banks=1 -set=icache_num_ways=2 -set=icache_bypass_enable=1 -set=icache_num_bypass=2 -set=icache_num_tag_bypass=2 -set=icache_tag_bypass_enable=1 -set=iccm_enable=0 -set=iccm_num_banks=4 -set=iccm_region=0xC -set=iccm_offset=0x0 -set=iccm_size=128 -set=lsu_stbuf_depth=4 -set=lsu_num_nbload=4 -set=load_to_use_plus1=0 -set=pic_2cycle=0 -set=pic_region=0xB -set=pic_offset=0 -set=pic_size=32 -set=pic_total_int=255 -set=timer_legal_en=1 -set=bitmanip_zba=1 -set=bitmanip_zbb=1 -set=bitmanip_zbc=1 -set=bitmanip_zbe=0 -set=bitmanip_zbf=0 -set=bitmanip_zbp=0 -set=bitmanip_zbr=0 -set=bitmanip_zbs=1 -set=user_mode=1 -set=pmp_entries=64 -set=smepmp=1 -set=reset_vec=0x90000000 -fpga_optimize=0 -snapshot=nwp_dccm64k 
# 
# To use this in a perf script, use 'require $RV_ROOT/configs/config.pl'
# Reference the hash via $config{name}..


%config = (
            'user_ec_rv_icg' => 'user_clock_gate',
            'regwidth' => '32',
            'max_mmode_perf_event' => '516',
            'protection' => {
                              'data_access_mask0' => '0xffffffff',
                              'inst_access_enable7' => '0x0',
                              'data_access_mask3' => '0xffffffff',
                              'data_access_addr7' => '0x00000000',
                              'inst_access_addr6' => '0x00000000',
                              'data_access_addr6' => '0x00000000',
                              'data_access_enable5' => '0x0',
                              'inst_access_mask7' => '0xffffffff',
                              'inst_access_enable2' => '0x0',
                              'inst_access_mask2' => '0xffffffff',
                              'inst_access_addr5' => '0x00000000',
                              'inst_access_enable5' => '0x0',
                              'data_access_mask1' => '0xffffffff',
                              'data_access_enable1' => '0x0',
                              'inst_access_addr0' => '0x00000000',
                              'data_access_enable6' => '0x0',
                              'inst_access_enable6' => '0x0',
                              'smepmp' => '1',
                              'data_access_mask5' => '0xffffffff',
                              'data_access_mask7' => '0xffffffff',
                              'data_access_enable3' => '0x0',
                              'inst_access_mask3' => '0xffffffff',
                              'inst_access_mask1' => '0xffffffff',
                              'inst_access_enable4' => '0x0',
                              'data_access_addr2' => '0x00000000',
                              'data_access_mask2' => '0xffffffff',
                              'data_access_enable7' => '0x0',
                              'inst_access_mask0' => '0xffffffff',
                              'inst_access_enable1' => '0x0',
                              'inst_access_addr2' => '0x00000000',
                              'data_access_addr1' => '0x00000000',
                              'inst_access_addr1' => '0x00000000',
                              'inst_access_addr3' => '0x00000000',
                              'data_access_mask4' => '0xffffffff',
                              'inst_access_mask6' => '0xffffffff',
                              'inst_access_mask5' => '0xffffffff',
                              'inst_access_addr7' => '0x00000000',
                              'inst_access_mask4' => '0xffffffff',
                              'data_access_enable4' => '0x0',
                              'inst_access_enable0' => '0x0',
                              'data_access_addr3' => '0x00000000',
                              'data_access_addr0' => '0x00000000',
                              'data_access_addr5' => '0x00000000',
                              'data_access_addr4' => '0x00000000',
                              'inst_access_addr4' => '0x00000000',
                              'data_access_enable2' => '0x0',
                              'data_access_mask6' => '0xffffffff',
                              'inst_access_enable3' => '0x0',
                              'data_access_enable0' => '0x0',
                              'pmp_entries' => '64'
                            },
            'harts' => 1,
            'even_odd_trigger_chains' => 'true',
            'bus' => {
                       'lsu_bus_prty' => '2',
                       'sb_bus_id' => '1',
                       'bus_prty_default' => '3',
                       'dma_bus_id' => '1',
                       'lsu_bus_tag' => 3,
                       'lsu_bus_id' => '1',
                       'sb_bus_tag' => '1',
                       'ifu_bus_id' => '1',
                       'dma_bus_prty' => '2',
                       'ifu_bus_tag' => '3',
                       'sb_bus_prty' => '2',
                       'ifu_bus_prty' => '2',
                       'dma_bus_tag' => '1'
                     },
            'memmap' => {
                          'unused_region4' => '0x40000000',
                          'unused_region3' => '0x50000000',
                          'external_data' => '0xe0580000',
                          'unused_region7' => '0x00000000',
                          'debug_sb_mem' => '0xa0580000',
                          'unused_region5' => '0x20000000',
                          'external_data_1' => '0xd0000000',
                          'unused_region0' => '0x80000000',
                          'unused_region6' => '0x10000000',
                          'unused_region2' => '0x60000000',
                          'consoleio' => '0xf0580000',
                          'serialio' => '0xf0580000',
                          'unused_region1' => '0x70000000'
                        },
            'csr' => {
                       'mfdht' => {
                                    'reset' => '0x0',
                                    'mask' => '0x0000003f',
                                    'shared' => 'true',
                                    'exists' => 'true',
                                    'comment' => 'Force Debug Halt Threshold',
                                    'number' => '0x7ce'
                                  },
                       'mhpmevent3' => {
                                         'exists' => 'true',
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff'
                                       },
                       'mitcnt1' => {
                                      'number' => '0x7d5',
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0',
                                      'exists' => 'true'
                                    },
                       'mimpid' => {
                                     'exists' => 'true',
                                     'mask' => '0x0',
                                     'reset' => '0x4'
                                   },
                       'mhartid' => {
                                      'exists' => 'true',
                                      'poke_mask' => '0xfffffff0',
                                      'mask' => '0x0',
                                      'reset' => '0x0'
                                    },
                       'mhpmevent6' => {
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0',
                                         'exists' => 'true'
                                       },
                       'meicidpl' => {
                                       'number' => '0xbcb',
                                       'reset' => '0x0',
                                       'mask' => '0xf',
                                       'exists' => 'true',
                                       'comment' => 'External interrupt claim id priority level.'
                                     },
                       'dicago' => {
                                     'reset' => '0x0',
                                     'debug' => 'true',
                                     'mask' => '0x0',
                                     'exists' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'number' => '0x7cb'
                                   },
                       'mcgc' => {
                                   'number' => '0x7f8',
                                   'exists' => 'true',
                                   'poke_mask' => '0x000003ff',
                                   'mask' => '0x000003ff',
                                   'reset' => '0x200'
                                 },
                       'mitbnd0' => {
                                      'exists' => 'true',
                                      'mask' => '0xffffffff',
                                      'reset' => '0xffffffff',
                                      'number' => '0x7d3'
                                    },
                       'dcsr' => {
                                   'mask' => '0x00008c04',
                                   'reset' => '0x40000003',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'poke_mask' => '0x00008dcc'
                                 },
                       'mitcnt0' => {
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0',
                                      'exists' => 'true',
                                      'number' => '0x7d2'
                                    },
                       'dmst' => {
                                   'number' => '0x7c4',
                                   'comment' => 'Memory synch trigger: Flush caches in debug mode.',
                                   'exists' => 'true',
                                   'mask' => '0x0',
                                   'debug' => 'true',
                                   'reset' => '0x0'
                                 },
                       'meipt' => {
                                    'number' => '0xbc9',
                                    'comment' => 'External interrupt priority threshold.',
                                    'exists' => 'true',
                                    'mask' => '0xf',
                                    'reset' => '0x0'
                                  },
                       'mhpmcounter3h' => {
                                            'mask' => '0xffffffff',
                                            'reset' => '0x0',
                                            'exists' => 'true'
                                          },
                       'mdccmect' => {
                                       'mask' => '0xffffffff',
                                       'reset' => '0x0',
                                       'exists' => 'true',
                                       'number' => '0x7f2'
                                     },
                       'mip' => {
                                  'poke_mask' => '0x70000888',
                                  'exists' => 'true',
                                  'mask' => '0x0',
                                  'reset' => '0x0'
                                },
                       'cycle' => {
                                    'exists' => 'false'
                                  },
                       'tselect' => {
                                      'exists' => 'true',
                                      'reset' => '0x0',
                                      'mask' => '0x3'
                                    },
                       'mvendorid' => {
                                        'reset' => '0x45',
                                        'mask' => '0x0',
                                        'exists' => 'true'
                                      },
                       'mitbnd1' => {
                                      'number' => '0x7d6',
                                      'reset' => '0xffffffff',
                                      'mask' => '0xffffffff',
                                      'exists' => 'true'
                                    },
                       'mhpmcounter6h' => {
                                            'exists' => 'true',
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff'
                                          },
                       'dicad1' => {
                                     'exists' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'debug' => 'true',
                                     'reset' => '0x0',
                                     'mask' => '0x3',
                                     'number' => '0x7ca'
                                   },
                       'dicad0' => {
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'mask' => '0xffffffff',
                                     'debug' => 'true',
                                     'reset' => '0x0',
                                     'number' => '0x7c9'
                                   },
                       'mhpmevent4' => {
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff',
                                         'exists' => 'true'
                                       },
                       'mfdhs' => {
                                    'number' => '0x7cf',
                                    'exists' => 'true',
                                    'comment' => 'Force Debug Halt Status',
                                    'reset' => '0x0',
                                    'mask' => '0x00000003'
                                  },
                       'mhpmcounter5h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'marchid' => {
                                      'exists' => 'true',
                                      'mask' => '0x0',
                                      'reset' => '0x00000010'
                                    },
                       'mhpmcounter5' => {
                                           'exists' => 'true',
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff'
                                         },
                       'instret' => {
                                      'exists' => 'false'
                                    },
                       'meicurpl' => {
                                       'exists' => 'true',
                                       'comment' => 'External interrupt current priority level.',
                                       'reset' => '0x0',
                                       'mask' => '0xf',
                                       'number' => '0xbcc'
                                     },
                       'dicawics' => {
                                       'number' => '0x7c8',
                                       'mask' => '0x0130fffc',
                                       'reset' => '0x0',
                                       'debug' => 'true',
                                       'comment' => 'Cache diagnostics.',
                                       'exists' => 'true'
                                     },
                       'miccmect' => {
                                       'number' => '0x7f1',
                                       'exists' => 'true',
                                       'reset' => '0x0',
                                       'mask' => '0xffffffff'
                                     },
                       'mitctl1' => {
                                      'reset' => '0x1',
                                      'mask' => '0x0000000f',
                                      'exists' => 'true',
                                      'number' => '0x7d7'
                                    },
                       'mhpmcounter4h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'misa' => {
                                   'reset' => '0x40001104',
                                   'mask' => '0x0',
                                   'exists' => 'true'
                                 },
                       'mscause' => {
                                      'exists' => 'true',
                                      'mask' => '0x0000000f',
                                      'reset' => '0x0',
                                      'number' => '0x7ff'
                                    },
                       'mpmc' => {
                                   'exists' => 'true',
                                   'reset' => '0x2',
                                   'mask' => '0x2',
                                   'number' => '0x7c6'
                                 },
                       'mhpmevent5' => {
                                         'exists' => 'true',
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff'
                                       },
                       'mitctl0' => {
                                      'reset' => '0x1',
                                      'mask' => '0x00000007',
                                      'exists' => 'true',
                                      'number' => '0x7d4'
                                    },
                       'mcountinhibit' => {
                                            'commnet' => 'Performance counter inhibit. One bit per counter.',
                                            'mask' => '0x7d',
                                            'reset' => '0x0',
                                            'poke_mask' => '0x7d',
                                            'exists' => 'true'
                                          },
                       'mstatus' => {
                                      'exists' => 'true',
                                      'mask' => '0x88',
                                      'reset' => '0x1800'
                                    },
                       'mcpc' => {
                                   'reset' => '0x0',
                                   'mask' => '0x0',
                                   'exists' => 'true',
                                   'comment' => 'Core pause',
                                   'number' => '0x7c2'
                                 },
                       'time' => {
                                   'exists' => 'false'
                                 },
                       'mrac' => {
                                   'number' => '0x7c0',
                                   'reset' => '0x0',
                                   'mask' => '0xffffffff',
                                   'exists' => 'true',
                                   'shared' => 'true',
                                   'comment' => 'Memory region io and cache control.'
                                 },
                       'mie' => {
                                  'mask' => '0x70000888',
                                  'reset' => '0x0',
                                  'exists' => 'true'
                                },
                       'mhpmcounter6' => {
                                           'mask' => '0xffffffff',
                                           'reset' => '0x0',
                                           'exists' => 'true'
                                         },
                       'mcounteren' => {
                                         'exists' => 'false'
                                       },
                       'mhpmcounter3' => {
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff',
                                           'exists' => 'true'
                                         },
                       'micect' => {
                                     'reset' => '0x0',
                                     'mask' => '0xffffffff',
                                     'exists' => 'true',
                                     'number' => '0x7f0'
                                   },
                       'mhpmcounter4' => {
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff',
                                           'exists' => 'true'
                                         },
                       'mfdc' => {
                                   'number' => '0x7f9',
                                   'reset' => '0x00070040',
                                   'mask' => '0x00071fff',
                                   'exists' => 'true'
                                 }
                     },
            'pic' => {
                       'pic_meip_offset' => '0x1000',
                       'pic_meipl_count' => 255,
                       'pic_mpiccfg_offset' => '0x3000',
                       'pic_meie_count' => 255,
                       'pic_total_int' => 255,
                       'pic_int_words' => 8,
                       'pic_size' => 32,
                       'pic_mpiccfg_mask' => '0x1',
                       'pic_meip_count' => 8,
                       'pic_meie_mask' => '0x1',
                       'pic_meipt_count' => 255,
                       'pic_meie_offset' => '0x2000',
                       'pic_mpiccfg_count' => 1,
                       'pic_meigwclr_offset' => '0x5000',
                       'pic_total_int_plus1' => 256,
                       'pic_meip_mask' => '0x0',
                       'pic_meigwctrl_mask' => '0x3',
                       'pic_meipl_mask' => '0xf',
                       'pic_meigwctrl_count' => 255,
                       'pic_meigwclr_mask' => '0x0',
                       'pic_offset' => '0',
                       'pic_base_addr' => '0xb0000000',
                       'pic_meipt_offset' => '0x3004',
                       'pic_meipl_offset' => '0x0000',
                       'pic_meigwctrl_offset' => '0x4000',
                       'pic_bits' => 15,
                       'pic_region' => '0xB',
                       'pic_meipt_mask' => '0x0',
                       'pic_meigwclr_count' => 255
                     },
            'nmi_vec' => '0x11110000',
            'testbench' => {
                             'RV_TOP' => '`TOP.rvtop_wrapper.rvtop',
                             'lderr_rollback' => '1',
                             'ext_addrwidth' => '32',
                             'ext_datawidth' => '64',
                             'clock_period' => '100',
                             'TOP' => 'tb_top',
                             'build_axi4' => 1,
                             'sterr_rollback' => '0',
                             'build_axi_native' => 1,
                             'CPU_TOP' => '`RV_TOP.veer',
                             'SDVT_AHB' => '0'
                           },
            'btb' => {
                       'btb_addr_hi' => 9,
                       'btb_size' => 512,
                       'btb_index3_lo' => 18,
                       'btb_index3_hi' => 25,
                       'btb_index1_hi' => 9,
                       'btb_fold2_index_hash' => 0,
                       'btb_index2_lo' => 10,
                       'btb_index2_hi' => 17,
                       'btb_btag_size' => 5,
                       'btb_array_depth' => 256,
                       'btb_enable' => '1',
                       'btb_btag_fold' => 0,
                       'btb_index1_lo' => '2',
                       'btb_toffset_size' => '12',
                       'btb_addr_lo' => '2'
                     },
            'num_mmode_perf_regs' => '4',
            'icache' => {
                          'icache_beat_addr_hi' => 5,
                          'icache_banks_way' => 2,
                          'icache_tag_cell' => 'ram_128x25',
                          'icache_ecc' => '1',
                          'icache_tag_depth' => 128,
                          'icache_scnd_last' => 6,
                          'icache_bypass_enable' => '1',
                          'icache_bank_hi' => 3,
                          'icache_num_bypass' => '2',
                          'icache_2banks' => '1',
                          'icache_data_width' => 64,
                          'icache_tag_num_bypass' => '2',
                          'icache_num_bypass_width' => 2,
                          'icache_data_index_lo' => 4,
                          'icache_size' => 16,
                          'icache_num_lines' => 256,
                          'icache_data_cell' => 'ram_512x71',
                          'icache_waypack' => '1',
                          'icache_num_beats' => 8,
                          'icache_bank_bits' => 1,
                          'icache_bank_lo' => 3,
                          'icache_num_ways' => 2,
                          'icache_tag_lo' => 13,
                          'icache_enable' => 1,
                          'icache_num_lines_bank' => '64',
                          'icache_index_hi' => 12,
                          'icache_fdata_width' => 71,
                          'icache_ln_sz' => 64,
                          'icache_tag_num_bypass_width' => 2,
                          'icache_num_lines_way' => '128',
                          'icache_beat_bits' => 3,
                          'icache_data_depth' => '512',
                          'icache_tag_bypass_enable' => '1',
                          'icache_status_bits' => 1,
                          'icache_bank_width' => 8,
                          'icache_tag_index_lo' => '6'
                        },
            'iccm' => {
                        'iccm_bank_index_lo' => 4,
                        'iccm_eadr' => '0xc001ffff',
                        'iccm_offset' => '0x0',
                        'iccm_data_cell' => 'ram_8192x39',
                        'iccm_region' => '0xC',
                        'iccm_ecc_width' => '7',
                        'iccm_bank_bits' => 2,
                        'iccm_rows' => '8192',
                        'iccm_size_128' => '',
                        'iccm_sadr' => '0xc0000000',
                        'iccm_num_banks_4' => '',
                        'iccm_reserved' => '0x1000',
                        'iccm_bank_hi' => 3,
                        'iccm_index_bits' => 13,
                        'iccm_bits' => 17,
                        'iccm_num_banks' => '4',
                        'iccm_size' => 128
                      },
            'core' => {
                        'user_mode' => '1',
                        'bitmanip_zbb' => 1,
                        'bitmanip_zbe' => 0,
                        'lsu_num_nbload_width' => '2',
                        'timer_legal_en' => '1',
                        'bitmanip_zba' => 1,
                        'bitmanip_zbc' => 1,
                        'dma_buf_depth' => '5',
                        'no_iccm_no_icache' => 'derived',
                        'iccm_only' => 'derived',
                        'bitmanip_zbs' => 1,
                        'lsu_num_nbload' => '4',
                        'bitmanip_zbp' => 0,
                        'fast_interrupt_redirect' => '1',
                        'bitmanip_zbr' => 0,
                        'bitmanip_zbf' => 0,
                        'div_new' => 1,
                        'lsu2dma' => 0,
                        'iccm_icache' => 'derived',
                        'icache_only' => 1,
                        'div_bit' => '4',
                        'lsu_stbuf_depth' => '4'
                      },
            'bht' => {
                       'bht_size' => 512,
                       'bht_ghr_hash_1' => '',
                       'bht_addr_hi' => 9,
                       'bht_hash_string' => '{hashin[8+1:2]^ghr[8-1:0]}// cf2',
                       'bht_addr_lo' => '2',
                       'bht_ghr_range' => '7:0',
                       'bht_array_depth' => 256,
                       'bht_ghr_size' => 8
                     },
            'config_key' => '32\'hdeadbeef',
            'tec_rv_icg' => 'clockhdr',
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
            'dccm' => {
                        'dccm_data_cell' => 'ram_4096x39',
                        'dccm_bank_bits' => 2,
                        'dccm_bits' => 16,
                        'dccm_data_width' => 32,
                        'dccm_region' => '0x3',
                        'dccm_size' => 64,
                        'dccm_num_banks' => '4',
                        'dccm_offset' => '0x00000',
                        'dccm_rows' => '4096',
                        'lsu_sb_bits' => 16,
                        'dccm_index_bits' => 12,
                        'dccm_reserved' => '0x1400',
                        'dccm_num_banks_4' => '',
                        'dccm_width_bits' => 2,
                        'dccm_enable' => '1',
                        'dccm_ecc_width' => 7,
                        'dccm_fdata_width' => 39,
                        'dccm_size_64' => '',
                        'dccm_byte_width' => '4',
                        'dccm_eadr' => '0x3000ffff',
                        'dccm_sadr' => '0x30000000'
                      },
            'triggers' => [
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
                            }
                          ],
            'physical' => '1',
            'xlen' => 32,
            'retstack' => {
                            'ret_stack_size' => '8'
                          },
            'target' => 'default',
            'numiregs' => '32',
            'reset_vec' => '0x90000000'
          );
1;
