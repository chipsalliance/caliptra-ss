package tb_top_pkg;

    `ifndef VERILATOR
      class bitflip_mask_generator #(
          int DATA_AND_ECC_W = 39
      );

        rand logic [DATA_AND_ECC_W-1:0] rand_sram_bitflip_mask;
        logic do_double_bitflip;
        constraint bitflip_c {
          if (do_double_bitflip) {
            $countones(rand_sram_bitflip_mask) == 2;
          } else {
            $countones(rand_sram_bitflip_mask) == 1;
          }
        }

    function new;
          this.rand_sram_bitflip_mask = '0;
          this.do_double_bitflip = 1'b0;
    endfunction

    function logic [DATA_AND_ECC_W-1:0] get_mask(bit do_double_bit = 1'b0);
          this.do_double_bitflip = do_double_bit;
          this.randomize();
          return this.rand_sram_bitflip_mask;
    endfunction

      endclass
    `else
  function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
        return 2 << ($urandom % (37)) | 39'(do_double_bit);
  endfunction
    `endif

  function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
        return 2 << ($urandom % (37)) | 39'(do_double_bit);
  endfunction 

      typedef struct packed {
        //  [3] - Double bit, DCCM Error Injection
        //  [2] - Single bit, DCCM Error Injection
        //  [1] - Double bit, ICCM Error Injection
        //  [0] - Single bit, ICCM Error Injection
        logic dccm_double_bit_error;
        logic dccm_single_bit_error;
        logic iccm_double_bit_error;
        logic iccm_single_bit_error;
      } veer_sram_error_injection_mode_t;

endpackage