#  NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
#  This is an automatically generated file by pascal on Di 16 Jun 2026 13:53:41 CEST
# 
#  cmd:    veer -target=default -set=ret_stack_size=8 -set=btb_enable=1 -set=btb_fullya=0 -set=btb_size=512 -set=bht_size=512 -set=div_bit=4 -set=div_new=1 -set=dccm_enable=1 -set=dccm_num_banks=4 -set=dccm_region=0x5 -set=dccm_offset=0x00000 -set=dccm_size=16 -set=dma_buf_depth=5 -set=fast_interrupt_redirect=1 -set=icache_enable=1 -set=icache_waypack=1 -set=icache_ecc=1 -set=icache_size=16 -set=icache_2banks=1 -set=icache_num_ways=2 -set=icache_bypass_enable=1 -set=icache_num_bypass=2 -set=icache_num_tag_bypass=2 -set=icache_tag_bypass_enable=1 -set=iccm_enable=0 -set=iccm_num_banks=4 -set=iccm_region=0x4 -set=iccm_offset=0x0 -set=iccm_size=128 -set=lsu_stbuf_depth=4 -set=lsu_num_nbload=4 -set=load_to_use_plus1=0 -set=lockstep_delay=2 -set=lockstep_enable=1 -set=lockstep_regfile_enable=1 -set=mubi_width=4 -set=mubi_true=0x6 -set=mubi_false=0x9 -set=pic_2cycle=0 -set=pic_region=0x6 -set=pic_offset=0 -set=pic_size=32 -set=pic_total_int=255 -set=timer_legal_en=1 -set=bitmanip_zba=1 -set=bitmanip_zbb=1 -set=bitmanip_zbc=1 -set=bitmanip_zbe=0 -set=bitmanip_zbf=0 -set=bitmanip_zbp=0 -set=bitmanip_zbr=0 -set=bitmanip_zbs=1 -set=user_mode=1 -set=pmp_entries=64 -set=smepmp=1 -set=reset_vec=0x80000000 -fpga_optimize=0 -snapshot=css_mcu0_dcls 
# 
# To use this in a perf script, use 'require $RV_ROOT/configs/config.pl'
# Reference the hash via $config{name}..


%config = (
            'physical' => '1',
            'retstack' => {
                            'ret_stack_size' => '8'
                          },
            'bus' => {
                       'lsu_bus_tag' => 3,
                       'bus_prty_default' => '3',
                       'ifu_bus_id' => '1',
                       'lsu_bus_prty' => '2',
                       'dma_bus_id' => '1',
                       'sb_bus_prty' => '2',
                       'sb_bus_id' => '1',
                       'sb_bus_tag' => '1',
                       'ifu_bus_prty' => '2',
                       'dma_bus_tag' => '1',
                       'ifu_bus_tag' => '3',
                       'dma_bus_prty' => '2',
                       'lsu_bus_id' => '1'
                     },
            'max_mmode_perf_event' => '516',
            'num_mmode_perf_regs' => '4',
            'regwidth' => '32',
            'memmap' => {
                          'serialio' => '0xf0580000',
                          'unused_region4' => '0x30000000',
                          'unused_region5' => '0x20000000',
                          'unused_region0' => '0xb0000000',
                          'unused_region6' => '0x10000000',
                          'unused_region7' => '0x00000000',
                          'external_data' => '0xe0580000',
                          'consoleio' => '0xf0580000',
                          'unused_region2' => '0x90000000',
                          'unused_region3' => '0x70000000',
                          'debug_sb_mem' => '0xc0580000',
                          'external_data_1' => '0xd0000000',
                          'unused_region1' => '0xa0000000'
                        },
            'reset_vec' => '0x80000000',
            'config_key' => '32\'hdeadbeef',
            'iccm' => {
                        'iccm_ecc_width' => '7',
                        'iccm_region' => '0x4',
                        'iccm_reserved' => '0x1000',
                        'iccm_offset' => '0x0',
                        'iccm_size' => 128,
                        'iccm_rows' => '8192',
                        'iccm_size_128' => '',
                        'iccm_bank_hi' => 3,
                        'iccm_data_cell' => 'ram_8192x39',
                        'iccm_sadr' => '0x40000000',
                        'iccm_bits' => 17,
                        'iccm_num_banks_4' => '',
                        'iccm_bank_index_lo' => 4,
                        'iccm_index_bits' => 13,
                        'iccm_num_banks' => '4',
                        'iccm_bank_bits' => 2,
                        'iccm_eadr' => '0x4001ffff'
                      },
            'target' => 'default',
            'dccm' => {
                        'dccm_enable' => '1',
                        'dccm_size_16' => '',
                        'dccm_rows' => '1024',
                        'dccm_size' => 16,
                        'dccm_offset' => '0x00000',
                        'dccm_byte_width' => '4',
                        'dccm_data_width' => 32,
                        'lsu_sb_bits' => 14,
                        'dccm_ecc_width' => 7,
                        'dccm_reserved' => '0x1400',
                        'dccm_region' => '0x5',
                        'dccm_width_bits' => 2,
                        'dccm_index_bits' => 10,
                        'dccm_bank_bits' => 2,
                        'dccm_num_banks' => '4',
                        'dccm_fdata_width' => 39,
                        'dccm_num_banks_4' => '',
                        'dccm_eadr' => '0x50003fff',
                        'dccm_data_cell' => 'ram_1024x39',
                        'dccm_bits' => 14,
                        'dccm_sadr' => '0x50000000'
                      },
            'protection' => {
                              'smepmp' => '1',
                              'inst_access_enable3' => '0x0',
                              'inst_access_addr4' => '0x00000000',
                              'data_access_mask3' => '0xffffffff',
                              'inst_access_mask7' => '0xffffffff',
                              'lockstep_regfile_enable' => '1',
                              'data_access_mask4' => '0xffffffff',
                              'inst_access_addr3' => '0x00000000',
                              'data_access_enable7' => '0x0',
                              'data_access_addr7' => '0x00000000',
                              'inst_access_addr6' => '0x00000000',
                              'inst_access_addr1' => '0x00000000',
                              'lockstep_delay' => '2',
                              'data_access_enable1' => '0x0',
                              'inst_access_mask2' => '0xffffffff',
                              'inst_access_enable0' => '0x0',
                              'mubi_false' => '0x9',
                              'data_access_enable6' => '0x0',
                              'lockstep_enable' => '1',
                              'data_access_addr5' => '0x00000000',
                              'data_access_addr0' => '0x00000000',
                              'data_access_mask6' => '0xffffffff',
                              'data_access_mask1' => '0xffffffff',
                              'data_access_enable4' => '0x0',
                              'inst_access_enable5' => '0x0',
                              'data_access_addr2' => '0x00000000',
                              'inst_access_mask5' => '0xffffffff',
                              'data_access_enable2' => '0x0',
                              'inst_access_mask0' => '0xffffffff',
                              'inst_access_enable7' => '0x0',
                              'inst_access_mask4' => '0xffffffff',
                              'data_access_addr3' => '0x00000000',
                              'inst_access_addr7' => '0x00000000',
                              'data_access_addr4' => '0x00000000',
                              'inst_access_mask3' => '0xffffffff',
                              'data_access_mask7' => '0xffffffff',
                              'data_access_enable3' => '0x0',
                              'mubi_true' => '0x6',
                              'data_access_mask0' => '0xffffffff',
                              'inst_access_enable2' => '0x0',
                              'data_access_mask5' => '0xffffffff',
                              'inst_access_mask6' => '0xffffffff',
                              'inst_access_mask1' => '0xffffffff',
                              'inst_access_enable4' => '0x0',
                              'data_access_enable5' => '0x0',
                              'inst_access_addr2' => '0x00000000',
                              'inst_access_enable6' => '0x0',
                              'pmp_entries' => '64',
                              'inst_access_addr0' => '0x00000000',
                              'inst_access_addr5' => '0x00000000',
                              'data_access_addr6' => '0x00000000',
                              'data_access_addr1' => '0x00000000',
                              'mubi_width' => '4',
                              'data_access_enable0' => '0x0',
                              'inst_access_enable1' => '0x0',
                              'data_access_mask2' => '0xffffffff'
                            },
            'xlen' => 32,
            'bht' => {
                       'bht_array_depth' => 256,
                       'bht_hash_string' => '{hashin[8+1:2]^ghr[8-1:0]}// cf2',
                       'bht_addr_hi' => 9,
                       'bht_size' => 512,
                       'bht_ghr_hash_1' => '',
                       'bht_addr_lo' => '2',
                       'bht_ghr_size' => 8,
                       'bht_ghr_range' => '7:0'
                     },
            'testbench' => {
                             'lderr_rollback' => '1',
                             'clock_period' => '100',
                             'CPU_TOP' => '`RV_TOP.veer',
                             'ext_datawidth' => '64',
                             'TOP' => 'tb_top',
                             'sterr_rollback' => '0',
                             'SDVT_AHB' => 0,
                             'build_axi4' => 1,
                             'build_axi_native' => 1,
                             'RV_TOP' => '`TOP.rvtop_wrapper.rvtop',
                             'ext_addrwidth' => '32'
                           },
            'tec_rv_icg' => 'clockhdr',
            'core' => {
                        'bitmanip_zbp' => 0,
                        'lsu_stbuf_depth' => '4',
                        'div_new' => 1,
                        'dma_buf_depth' => '5',
                        'div_bit' => '4',
                        'bitmanip_zba' => 1,
                        'bitmanip_zbe' => 0,
                        'icache_only' => 1,
                        'bitmanip_zbb' => 1,
                        'lsu2dma' => 0,
                        'iccm_only' => 'derived',
                        'lsu_num_nbload' => '4',
                        'no_iccm_no_icache' => 'derived',
                        'bitmanip_zbf' => 0,
                        'fast_interrupt_redirect' => '1',
                        'lsu_num_nbload_width' => '2',
                        'bitmanip_zbc' => 1,
                        'user_mode' => '1',
                        'timer_legal_en' => '1',
                        'bitmanip_zbr' => 0,
                        'bitmanip_zbs' => 1,
                        'iccm_icache' => 'derived'
                      },
            'harts' => 1,
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
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ]
                            }
                          ],
            'even_odd_trigger_chains' => 'true',
            'pic' => {
                       'pic_mpiccfg_mask' => '0x1',
                       'pic_meigwclr_offset' => '0x5000',
                       'pic_mpiccfg_count' => 1,
                       'pic_meipl_count' => 255,
                       'pic_total_int_plus1' => 256,
                       'pic_size' => 32,
                       'pic_mpiccfg_offset' => '0x3000',
                       'pic_meipl_mask' => '0xf',
                       'pic_meie_mask' => '0x1',
                       'pic_total_int' => 255,
                       'pic_region' => '0x6',
                       'pic_meipt_offset' => '0x3004',
                       'pic_meip_mask' => '0x0',
                       'pic_meigwctrl_offset' => '0x4000',
                       'pic_meie_count' => 255,
                       'pic_meipt_count' => 255,
                       'pic_meip_offset' => '0x1000',
                       'pic_meigwclr_count' => 255,
                       'pic_meigwctrl_mask' => '0x3',
                       'pic_meigwctrl_count' => 255,
                       'pic_meip_count' => 8,
                       'pic_meie_offset' => '0x2000',
                       'pic_base_addr' => '0x60000000',
                       'pic_meigwclr_mask' => '0x0',
                       'pic_meipl_offset' => '0x0000',
                       'pic_bits' => 15,
                       'pic_int_words' => 8,
                       'pic_meipt_mask' => '0x0',
                       'pic_offset' => '0'
                     },
            'user_ec_rv_icg' => 'user_clock_gate',
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
            'icache' => {
                          'icache_beat_addr_hi' => 5,
                          'icache_size' => 16,
                          'icache_ecc' => '1',
                          'icache_tag_depth' => 128,
                          'icache_tag_num_bypass' => '2',
                          'icache_waypack' => '1',
                          'icache_tag_bypass_enable' => '1',
                          'icache_beat_bits' => 3,
                          'icache_tag_cell' => 'ram_128x25',
                          'icache_banks_way' => 2,
                          'icache_num_ways' => 2,
                          'icache_tag_index_lo' => '6',
                          'icache_num_bypass_width' => 2,
                          'icache_num_lines_way' => '128',
                          'icache_num_lines' => 256,
                          'icache_data_depth' => '512',
                          'icache_enable' => 1,
                          'icache_index_hi' => 12,
                          'icache_tag_lo' => 13,
                          'icache_num_beats' => 8,
                          'icache_2banks' => '1',
                          'icache_data_cell' => 'ram_512x71',
                          'icache_num_lines_bank' => '64',
                          'icache_bank_width' => 8,
                          'icache_fdata_width' => 71,
                          'icache_tag_num_bypass_width' => 2,
                          'icache_bank_lo' => 3,
                          'icache_data_index_lo' => 4,
                          'icache_bank_hi' => 3,
                          'icache_bank_bits' => 1,
                          'icache_status_bits' => 1,
                          'icache_ln_sz' => 64,
                          'icache_scnd_last' => 6,
                          'icache_data_width' => 64,
                          'icache_num_bypass' => '2',
                          'icache_bypass_enable' => '1'
                        },
            'nmi_vec' => '0x11110000',
            'numiregs' => '32',
            'btb' => {
                       'btb_size' => 512,
                       'btb_index3_lo' => 18,
                       'btb_addr_hi' => 9,
                       'btb_index1_lo' => '2',
                       'btb_btag_fold' => 0,
                       'btb_index2_lo' => 10,
                       'btb_enable' => '1',
                       'btb_index2_hi' => 17,
                       'btb_array_depth' => 256,
                       'btb_fold2_index_hash' => 0,
                       'btb_btag_size' => 5,
                       'btb_index3_hi' => 25,
                       'btb_index1_hi' => 9,
                       'btb_addr_lo' => '2',
                       'btb_toffset_size' => '12'
                     },
            'csr' => {
                       'mpmc' => {
                                   'number' => '0x7c6',
                                   'exists' => 'true',
                                   'reset' => '0x2',
                                   'mask' => '0x2'
                                 },
                       'dmst' => {
                                   'comment' => 'Memory synch trigger: Flush caches in debug mode.',
                                   'debug' => 'true',
                                   'exists' => 'true',
                                   'number' => '0x7c4',
                                   'reset' => '0x0',
                                   'mask' => '0x0'
                                 },
                       'time' => {
                                   'exists' => 'false'
                                 },
                       'mhpmcounter5h' => {
                                            'reset' => '0x0',
                                            'exists' => 'true',
                                            'mask' => '0xffffffff'
                                          },
                       'mrac' => {
                                   'shared' => 'true',
                                   'comment' => 'Memory region io and cache control.',
                                   'exists' => 'true',
                                   'number' => '0x7c0',
                                   'reset' => '0x0',
                                   'mask' => '0xffffffff'
                                 },
                       'mcpc' => {
                                   'comment' => 'Core pause',
                                   'reset' => '0x0',
                                   'number' => '0x7c2',
                                   'exists' => 'true',
                                   'mask' => '0x0'
                                 },
                       'mfdc' => {
                                   'mask' => '0x00071fff',
                                   'reset' => '0x00070040',
                                   'number' => '0x7f9',
                                   'exists' => 'true'
                                 },
                       'dicad0' => {
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'mask' => '0xffffffff',
                                     'exists' => 'true',
                                     'number' => '0x7c9',
                                     'reset' => '0x0'
                                   },
                       'misa' => {
                                   'mask' => '0x0',
                                   'exists' => 'true',
                                   'reset' => '0x40001104'
                                 },
                       'meipt' => {
                                    'reset' => '0x0',
                                    'number' => '0xbc9',
                                    'exists' => 'true',
                                    'mask' => '0xf',
                                    'comment' => 'External interrupt priority threshold.'
                                  },
                       'mhpmcounter6' => {
                                           'reset' => '0x0',
                                           'exists' => 'true',
                                           'mask' => '0xffffffff'
                                         },
                       'tselect' => {
                                      'mask' => '0x3',
                                      'exists' => 'true',
                                      'reset' => '0x0'
                                    },
                       'meicurpl' => {
                                       'comment' => 'External interrupt current priority level.',
                                       'mask' => '0xf',
                                       'reset' => '0x0',
                                       'exists' => 'true',
                                       'number' => '0xbcc'
                                     },
                       'dicawics' => {
                                       'debug' => 'true',
                                       'comment' => 'Cache diagnostics.',
                                       'mask' => '0x0130fffc',
                                       'reset' => '0x0',
                                       'number' => '0x7c8',
                                       'exists' => 'true'
                                     },
                       'mcgc' => {
                                   'poke_mask' => '0x000003ff',
                                   'reset' => '0x200',
                                   'exists' => 'true',
                                   'number' => '0x7f8',
                                   'mask' => '0x000003ff'
                                 },
                       'mitcnt0' => {
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0',
                                      'number' => '0x7d2',
                                      'exists' => 'true'
                                    },
                       'mhpmevent5' => {
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0',
                                         'exists' => 'true'
                                       },
                       'mcounteren' => {
                                         'exists' => 'false'
                                       },
                       'mhartid' => {
                                      'poke_mask' => '0xfffffff0',
                                      'exists' => 'true',
                                      'reset' => '0x0',
                                      'mask' => '0x0'
                                    },
                       'mip' => {
                                  'exists' => 'true',
                                  'reset' => '0x0',
                                  'mask' => '0x0',
                                  'poke_mask' => '0x70000888'
                                },
                       'dicad1' => {
                                     'comment' => 'Cache diagnostics.',
                                     'debug' => 'true',
                                     'mask' => '0x3',
                                     'exists' => 'true',
                                     'number' => '0x7ca',
                                     'reset' => '0x0'
                                   },
                       'mhpmcounter4' => {
                                           'mask' => '0xffffffff',
                                           'exists' => 'true',
                                           'reset' => '0x0'
                                         },
                       'mie' => {
                                  'mask' => '0x70000888',
                                  'reset' => '0x0',
                                  'exists' => 'true'
                                },
                       'dcsr' => {
                                   'debug' => 'true',
                                   'poke_mask' => '0x00008dcc',
                                   'mask' => '0x00008c04',
                                   'reset' => '0x40000003',
                                   'exists' => 'true'
                                 },
                       'mhpmcounter3h' => {
                                            'reset' => '0x0',
                                            'exists' => 'true',
                                            'mask' => '0xffffffff'
                                          },
                       'mitctl0' => {
                                      'reset' => '0x1',
                                      'exists' => 'true',
                                      'number' => '0x7d4',
                                      'mask' => '0x00000007'
                                    },
                       'mitbnd1' => {
                                      'exists' => 'true',
                                      'number' => '0x7d6',
                                      'reset' => '0xffffffff',
                                      'mask' => '0xffffffff'
                                    },
                       'dicago' => {
                                     'reset' => '0x0',
                                     'exists' => 'true',
                                     'number' => '0x7cb',
                                     'mask' => '0x0',
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.'
                                   },
                       'marchid' => {
                                      'mask' => '0x0',
                                      'exists' => 'true',
                                      'reset' => '0x00000010'
                                    },
                       'mstatus' => {
                                      'reset' => '0x1800',
                                      'exists' => 'true',
                                      'mask' => '0x88'
                                    },
                       'mhpmevent6' => {
                                         'mask' => '0xffffffff',
                                         'exists' => 'true',
                                         'reset' => '0x0'
                                       },
                       'micect' => {
                                     'mask' => '0xffffffff',
                                     'number' => '0x7f0',
                                     'exists' => 'true',
                                     'reset' => '0x0'
                                   },
                       'mhpmcounter4h' => {
                                            'mask' => '0xffffffff',
                                            'exists' => 'true',
                                            'reset' => '0x0'
                                          },
                       'mfdht' => {
                                    'shared' => 'true',
                                    'comment' => 'Force Debug Halt Threshold',
                                    'number' => '0x7ce',
                                    'exists' => 'true',
                                    'reset' => '0x0',
                                    'mask' => '0x0000003f'
                                  },
                       'meicidpl' => {
                                       'comment' => 'External interrupt claim id priority level.',
                                       'mask' => '0xf',
                                       'reset' => '0x0',
                                       'exists' => 'true',
                                       'number' => '0xbcb'
                                     },
                       'mhpmevent4' => {
                                         'mask' => '0xffffffff',
                                         'reset' => '0x0',
                                         'exists' => 'true'
                                       },
                       'mfdhs' => {
                                    'reset' => '0x0',
                                    'number' => '0x7cf',
                                    'exists' => 'true',
                                    'mask' => '0x00000003',
                                    'comment' => 'Force Debug Halt Status'
                                  },
                       'mcountinhibit' => {
                                            'poke_mask' => '0x7d',
                                            'commnet' => 'Performance counter inhibit. One bit per counter.',
                                            'exists' => 'true',
                                            'reset' => '0x0',
                                            'mask' => '0x7d'
                                          },
                       'miccmect' => {
                                       'mask' => '0xffffffff',
                                       'reset' => '0x0',
                                       'number' => '0x7f1',
                                       'exists' => 'true'
                                     },
                       'instret' => {
                                      'exists' => 'false'
                                    },
                       'mhpmcounter3' => {
                                           'mask' => '0xffffffff',
                                           'reset' => '0x0',
                                           'exists' => 'true'
                                         },
                       'mitcnt1' => {
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0',
                                      'number' => '0x7d5',
                                      'exists' => 'true'
                                    },
                       'mscause' => {
                                      'exists' => 'true',
                                      'number' => '0x7ff',
                                      'reset' => '0x0',
                                      'mask' => '0x0000000f'
                                    },
                       'mhpmevent3' => {
                                         'exists' => 'true',
                                         'reset' => '0x0',
                                         'mask' => '0xffffffff'
                                       },
                       'mhpmcounter5' => {
                                           'mask' => '0xffffffff',
                                           'exists' => 'true',
                                           'reset' => '0x0'
                                         },
                       'cycle' => {
                                    'exists' => 'false'
                                  },
                       'mimpid' => {
                                     'mask' => '0x0',
                                     'reset' => '0x4',
                                     'exists' => 'true'
                                   },
                       'mhpmcounter6h' => {
                                            'mask' => '0xffffffff',
                                            'exists' => 'true',
                                            'reset' => '0x0'
                                          },
                       'mitbnd0' => {
                                      'mask' => '0xffffffff',
                                      'reset' => '0xffffffff',
                                      'number' => '0x7d3',
                                      'exists' => 'true'
                                    },
                       'mitctl1' => {
                                      'reset' => '0x1',
                                      'exists' => 'true',
                                      'number' => '0x7d7',
                                      'mask' => '0x0000000f'
                                    },
                       'mvendorid' => {
                                        'exists' => 'true',
                                        'reset' => '0x45',
                                        'mask' => '0x0'
                                      },
                       'mdccmect' => {
                                       'mask' => '0xffffffff',
                                       'reset' => '0x0',
                                       'exists' => 'true',
                                       'number' => '0x7f2'
                                     }
                     }
          );
1;
