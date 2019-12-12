// sva_fpu_fma.sv

parameter FP = 32;              // Floating point bit selection
parameter M = 1;                // Maximum register row size
parameter N = 1;                // Maximum register column size
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

// Floating point data type
typedef struct packed {
    bit sign;
    bit [EXPBITS-1:0] exponent;
    bit [MANBITS-1:0] mantissa;
} float_sp;


module sva_fpu_fma (clk, rst, float_0_busy_in, float_1_busy_in, busy_out, float_0_req_in, float_0_req_out, float_1_req_in, float_1_req_out, float_0_in, float_0_out, float_1_in, float_1_out, float_answer_out, ready_answer_out, overflow_out, underflow_out, state_out);
    
    // Ports declarations
    input clk, rst, ready_answer_out, overflow_out, underflow_out;
    input float_0_busy_in, float_1_busy_in, busy_out;
    input float_0_req_in, float_1_req_in, float_0_req_out, float_1_req_out;
    input float_sp float_0_in, float_0_out, float_1_in, float_1_out, float_answer_out;
    input fma_state_e state_out;

    // Default clocking and reset
    default clocking c0 @(posedge clk); endclocking
    default disable iff (rst);

    // Sequences
    sequence multiply (in1, in2, expected);
        ((float_0_in == in1) & (float_1_in == in2) & float_0_req_in & float_1_req_in)
            ##[1:8] (float_answer_out == expected);// & (state_out == OUTPUT);
    endsequence
	
    /////////////////
    // Assumptions //
	/////////////////
    assume_no_load_state:           assume property ( state_out != LOAD );
    assume_nonzero_input:           assume property ( ({float_0_in.exponent, float_0_in.mantissa} != '0) && ({float_1_in.exponent, float_1_in.mantissa} != '0) );
    assume_tie_requests:            assume property ( float_0_req_in == float_1_req_in );
    assume_stable_input0:           assume property ( $rose(float_0_req_in) |-> ($stable(float_0_in) & $stable(float_1_in))[*2] ##1 !float_0_req_in[*6] );
	assume_stable_input1:           assume property ( $rose(float_1_req_in) |-> ($stable(float_0_in) & $stable(float_1_in))[*2] ##1 !float_1_req_in[*6] );
	// Want to make float_0_in and float_1_in change simultaneouslly
	assume_input_change_concurrent: assume property ($changed(float_0_in) |-> $changed(float_1_in));
	// We need busy_in signal to make the FSM go to OUTPUT state. But we don't want to keep these signal high forever.
	assume_set_proper_busy_in:      assume property (state_out == OUTPUT |-> (float_0_busy_in == 1'b1 & float_1_busy_in == 1'b1)[*2] ##1 (float_0_busy_in != 1'b1 & float_1_busy_in != 1'b1));
	// Hard to constraint the leagal inputs and generate valid multiplication result. So, for verify the basic multiplication, just neglect ERROR now.
	assume_no_ERROR_state:          assume property (state_out != ERROR); 

    /////////////////
    // Covers      //
	/////////////////	
	
    // Covers - Make sure interesting value is valid
    answer_ready_cover:            cover property ( $rose(ready_answer_out) );
    overflow_produced_cover:       cover property ( $rose(overflow_out) );
    underflow_produced_cover:      cover property ( $rose(underflow_out) );
	
	// Covers - Make sure all states and transitions reachable
    state_idle_cover:              cover property ( state_out == IDLE );
    state_load_cover:              cover property ( state_out == LOAD );
    state_multiply_cover:          cover property ( state_out == MULTIPLY );
    state_align_cover:             cover property ( state_out == ALIGN );
    state_accumulate_cover:        cover property ( state_out == ACCUMULATE );
    state_normalize_cover:         cover property ( state_out == NORMALIZE );
    state_output_cover:            cover property ( state_out == OUTPUT );
    state_error_cover:             cover property ( state_out == ERROR );
    state_idle_to_idle_cover:      cover property ( (state_out == IDLE) |=> (state_out == IDLE) );
    state_idle_to_load_cover:      cover property ( (state_out == IDLE) |=> (state_out == LOAD) );
    state_idle_to_multiply_cover:  cover property ( (state_out == IDLE) |=> (state_out == MULTIPLY) );
    state_idle_to_error_cover:     cover property ( (state_out == IDLE) |=> (state_out == ERROR) );
    state_load_to_load_cover:      cover property ( (state_out == LOAD) |=> (state_out == LOAD) );
    state_load_to_multiply_cover:  cover property ( (state_out == LOAD) |=> (state_out == MULTIPLY) );
    state_load_to_error_cover:     cover property ( (state_out == LOAD) |=> (state_out == ERROR) );
    state_output_to_output_cover:  cover property ( (state_out == OUTPUT) |=> (state_out == OUTPUT) );
    state_output_to_idle_cover:    cover property ( (state_out == OUTPUT) |=> (state_out == IDLE) );
    state_output_to_error_cover:   cover property ( (state_out == OUTPUT) |=> (state_out == ERROR) );
	
	// Covers - Check for multiplication for different kinds of input
    cover_multiply_pos1_x_pos1:      cover property ( multiply(32'h3f800000, 32'h3f800000, 32'h3f800000) ); // 1 * 1 = 1
    bad_cover_multiply_pos1_x_pos1:  cover property ( multiply(32'h3f800000, 32'h3f800000, 32'h41200000) ); // 1 * 1 = 10
	cover_multiply_pos15_x_neg20:    cover property ( multiply(32'h41700000, 32'hc1a00000, 32'hc3960000) ); // 15 * (-20) = -300
	cover_multiply_neg26_x_pos31:    cover property ( multiply(32'hc1d00000, 32'h41f80000, 32'hc4498000) ); // (-26) * 31 = -806

    
    /////////////////
    // Assertions  //
	/////////////////
	assert_answer_produced:        assert property ( float_0_req_in & float_1_req_in |-> ##[1:7] (state_out == OUTPUT) ##1 $rose(ready_answer_out) );
	liveness_back_to_IDLE:         assert property (state_out == IDLE |-> s_eventually(state_out == IDLE));
	assert_busy_output_check:      assert property (state_out != IDLE |=> busy_out == 1'b1);

endmodule : sva_fpu_fma