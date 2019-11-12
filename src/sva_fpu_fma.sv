// sva_fpu_fma.sv

parameter FP = 32;              // Floating point bit selection
parameter M = 3;                // Maximum register row size
parameter N = 3;                // Maximum register column size
parameter MBITS = $clog2(M)-1;  // Register row bits
parameter NBITS = $clog2(N)-1;  // Register column bits
parameter EXPBITS = 8;          // 8 exponent bits
parameter MANBITS = 23;         // 23 mantissa bits
parameter MIN_EXP = -128;       // 8-bit exponent minimum
parameter MAX_EXP = 127;        // 8-bit exponent maximum
parameter EXP_OFFSET = 127;     // 8-bit exponent offset

// Boolean data type
typedef enum bit {
    FALSE, 
    TRUE
} bool_e;

// FMA states
typedef enum bit [2:0] {
    IDLE,
    LOAD,
    MULTIPLY,
    ALIGN,
    ACCUMULATE,
    NORMALIZE,
    OUTPUT,
    ERROR
} fma_state_e;

/*// Floating point data type
typedef struct packed {
    bit sign;
    bit [EXPBITS-1:0] exponent;
    bit [MANBITS-1:0] mantissa;
} float_sp;

// Internal floating point data type
typedef struct packed {
    bit sign;
    bit [EXPBITS-1:0] exponent;
    bit [2*MANBITS+3:0] mantissa;
} internal_float_sp;*/

module sva_fpu_fma (clk, rst, float_0_busy_in, float_1_busy_in, busy_out, float_0_req_in, float_0_req_out, float_1_req_in, float_1_req_out, float_0_in, float_0_out, float_1_in, float_1_out, float_answer_out, ready_answer_out, overflow_out, underflow_out);
    
    // Ports declarations
    input clk, rst, ready_answer_out, overflow_out, underflow_out;
    input float_0_busy_in, float_1_busy_in, busy_out;
    input float_0_req_in, float_1_req_in, float_0_req_out, float_1_req_out;
    input shortreal float_0_in, float_0_out, float_1_in, float_1_out, float_answer_out;

    // Default clocking and reset
    default clocking c0 @(posedge clk); endclocking
    default disable iff (rst);

    // Covers
    answer_ready_cover:        cover property( $rose(ready_answer_out) );
    overflow_produced_cover:   cover property( $rose(overflow_out) );
    underflow_produced_cover:  cover property( $rose(underflow_out) );

endmodule : sva_fpu_fma