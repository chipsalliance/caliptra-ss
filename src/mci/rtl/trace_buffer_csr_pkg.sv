// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package trace_buffer_csr_pkg;

    localparam TRACE_BUFFER_CSR_DATA_WIDTH = 32;
    localparam TRACE_BUFFER_CSR_MIN_ADDR_WIDTH = 5;

    typedef struct packed{
        logic next;
    } trace_buffer_csr__STATUS__wrapped__in_t;

    typedef struct packed{
        logic next;
    } trace_buffer_csr__STATUS__valid_data__in_t;

    typedef struct packed{
        trace_buffer_csr__STATUS__wrapped__in_t wrapped;
        trace_buffer_csr__STATUS__valid_data__in_t valid_data;
    } trace_buffer_csr__STATUS__in_t;

    typedef struct packed{
        logic [31:0] next;
    } trace_buffer_csr__CONFIG__trace_buffer_depth__in_t;

    typedef struct packed{
        trace_buffer_csr__CONFIG__trace_buffer_depth__in_t trace_buffer_depth;
    } trace_buffer_csr__CONFIG__in_t;

    typedef struct packed{
        logic [31:0] next;
    } trace_buffer_csr__DATA__data__in_t;

    typedef struct packed{
        trace_buffer_csr__DATA__data__in_t data;
    } trace_buffer_csr__DATA__in_t;

    typedef struct packed{
        logic [31:0] next;
    } trace_buffer_csr__WRITE_PTR__ptr__in_t;

    typedef struct packed{
        trace_buffer_csr__WRITE_PTR__ptr__in_t ptr;
    } trace_buffer_csr__WRITE_PTR__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
    } trace_buffer_csr__READ_PTR__ptr__in_t;

    typedef struct packed{
        trace_buffer_csr__READ_PTR__ptr__in_t ptr;
    } trace_buffer_csr__READ_PTR__in_t;

    typedef struct packed{
        logic rst_b;
        trace_buffer_csr__STATUS__in_t STATUS;
        trace_buffer_csr__CONFIG__in_t CONFIG;
        trace_buffer_csr__DATA__in_t DATA;
        trace_buffer_csr__WRITE_PTR__in_t WRITE_PTR;
        trace_buffer_csr__READ_PTR__in_t READ_PTR;
    } trace_buffer_csr__in_t;

    typedef struct packed{
        logic value;
    } trace_buffer_csr__STATUS__wrapped__out_t;

    typedef struct packed{
        logic value;
    } trace_buffer_csr__STATUS__valid_data__out_t;

    typedef struct packed{
        trace_buffer_csr__STATUS__wrapped__out_t wrapped;
        trace_buffer_csr__STATUS__valid_data__out_t valid_data;
    } trace_buffer_csr__STATUS__out_t;

    typedef struct packed{
        logic [31:0] value;
    } trace_buffer_csr__CONFIG__trace_buffer_depth__out_t;

    typedef struct packed{
        trace_buffer_csr__CONFIG__trace_buffer_depth__out_t trace_buffer_depth;
    } trace_buffer_csr__CONFIG__out_t;

    typedef struct packed{
        logic [31:0] value;
    } trace_buffer_csr__DATA__data__out_t;

    typedef struct packed{
        trace_buffer_csr__DATA__data__out_t data;
    } trace_buffer_csr__DATA__out_t;

    typedef struct packed{
        logic [31:0] value;
    } trace_buffer_csr__WRITE_PTR__ptr__out_t;

    typedef struct packed{
        trace_buffer_csr__WRITE_PTR__ptr__out_t ptr;
    } trace_buffer_csr__WRITE_PTR__out_t;

    typedef struct packed{
        logic [31:0] value;
    } trace_buffer_csr__READ_PTR__ptr__out_t;

    typedef struct packed{
        trace_buffer_csr__READ_PTR__ptr__out_t ptr;
    } trace_buffer_csr__READ_PTR__out_t;

    typedef struct packed{
        trace_buffer_csr__STATUS__out_t STATUS;
        trace_buffer_csr__CONFIG__out_t CONFIG;
        trace_buffer_csr__DATA__out_t DATA;
        trace_buffer_csr__WRITE_PTR__out_t WRITE_PTR;
        trace_buffer_csr__READ_PTR__out_t READ_PTR;
    } trace_buffer_csr__out_t;

    localparam TRACE_BUFFER_CSR_ADDR_WIDTH = 32'd5;

endpackage