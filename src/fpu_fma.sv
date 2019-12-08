// fpu_fma.sv
// ----------------------------------------------------------------------------
//   Author: Alex Olson
//     Date: July 2019
//
// Desciption:
// ----------------------------------------------------------------------------
// Fused-Multiply Accumulate core designed to connect to 4 neighbors within a
// hypercube. The answer (accumulator) is output when the internal accumulation
// count reaches the size of the matrix (N).
//
// 
//         Single FMA unit
//              float_1
//                |
//                v
//  float_0 ---> FMA ---> float_0
//                | \
//                v  ans
//              float_1
//
// ------------------------------------------------------------------------------

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

// Internal floating point data type
typedef struct packed {
    bit sign;
    bit [EXPBITS-1:0] exponent;
    bit [2*MANBITS+3:0] mantissa;
} internal_float_sp;        


module fpu_fma
(
    // Control Signals
    input           clk,                // Clock
    input           rst,                // Synchronous reset active high

    // Busy Signals
    input  bit      float_0_busy_in,    // float 0 neighbor busy state
    input  bit      float_1_busy_in,    // float 1 neighbor busy state
    output bit      busy_out,           // Output busy state to neighbors

    // Data request signals
    input  bit      float_0_req_in,     // float 0 input request
    output bit      float_0_req_out,    // float 0 output request
    input  bit      float_1_req_in,     // float 1 input request
    output bit      float_1_req_out,    // float 1 output request

    // Float I/O
    input  float_sp float_0_in,         // float 0 input
    output float_sp float_0_out,        // float 0 output
    input  float_sp float_1_in,         // float 1 input
    output float_sp float_1_out,        // float 1 output

    // Answer output
    output float_sp float_answer_out,   // Answer float output
    output bit      ready_answer_out,   // Signal answer output ready
    output bit      overflow_out,       // Signal overflow condition was produced
    output bit      underflow_out,      // Signal underflow condition was produced
    output fma_state_e state_out        // Output state for formal tools
);

    bit [NBITS:0] count;                // Internal count of when to output accumulator
    bit error_in;                       // Detect a faulty input
    bit error_generated;                // Detect if any arithmetic produced an error

    bit busy;                           // Current state of the FMA unit
    float_sp float_0;                   // Floating point multiplier
    float_sp float_1;                   // Floating point multiplicand
    internal_float_sp accum;            // Persistent accumulator, cleared after count maxes out
    internal_float_sp product;          // Temporary product to go into accumulator
    fma_state_e state, next_state;      // FMA states

    // Broadcast busy state to neighbors
    assign busy_out = busy;

    // Check for input errors (denormalized numbers, +infinity, -infinity, NaN)
    assign error_in = ((float_0_in.mantissa && !float_0_in.exponent) || float_0_in.exponent == '1) ||
                      ((float_1_in.mantissa && !float_1_in.exponent) || float_1_in.exponent == '1);

    // Error detection
    assign error_generated = (($signed(product.exponent) >= MAX_EXP) || ($signed(product.exponent) <= MIN_EXP));
    assign overflow_out = ($signed(product.exponent) >= MAX_EXP);
    assign underflow_out = ($signed(product.exponent) <= MIN_EXP);

    // State machine driver
    always_ff @(posedge clk) begin
        state <= rst ? IDLE : next_state;
    end
    assign state_out = state;

    // Next state logic
    always_comb begin
        unique case (state)
            IDLE: begin
                // Check for input error
                if (error_in) begin
                    next_state <= ERROR;
                end
                else if (float_0_req_in & float_1_req_in) begin
                    next_state <= MULTIPLY;
                end
                else if (float_0_req_in | float_1_req_in) begin
                    next_state <= LOAD;
                end
                else begin
                    next_state <= IDLE;
                end
            end
            LOAD: begin
                // Check for input error
                if (error_in) begin
                    next_state <= ERROR;
                end
                else if (float_0_req_in | float_1_req_in) begin
                    next_state <= MULTIPLY;
                end
                else begin
                    next_state <= LOAD;
                end
            end
            MULTIPLY: begin
                next_state <= ALIGN;
            end
            ALIGN: begin
                next_state <= ACCUMULATE;
            end
            ACCUMULATE: begin
                next_state <= NORMALIZE;
            end
            NORMALIZE: begin
                next_state <= OUTPUT;
            end
            OUTPUT: begin
                // Check for overflow/underflow in the result
                if (error_generated) begin
                    next_state <= ERROR;
                end
                else begin
                    // Hold output until neighbors can receive next input signals
                    if (float_0_busy_in | float_1_busy_in) begin
                        next_state <= OUTPUT;
                    end
                    else begin
                        next_state <= IDLE;
                    end
               end
            end
            ERROR: begin 
                next_state <= IDLE;
            end
        endcase
    end

    // Clocked logic and I/O
    always_ff @(posedge clk) begin
        if (rst) begin
            count <= '0;
            busy <= FALSE;
            float_0_req_out <= FALSE;
            float_1_req_out <= FALSE;
            float_0_out <= '0;
            float_1_out <= '0;
            float_0 <= '0;
            float_1 <= '0;
            accum <= '0;
            product <= '0;
            float_answer_out <= '0;
            ready_answer_out <= FALSE;
        end
        else begin
            unique case (state)
                IDLE: begin
                    count <= count;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    // If a start signal is recieved, capture the associated input
                    if (float_0_req_in & float_1_req_in) begin
                        busy <= TRUE;
                        float_0.sign <= float_0_in.sign;
                        float_0.exponent <= float_0_in.exponent;
                        float_0.mantissa <= float_0_in.mantissa;
                        float_1.sign <= float_1_in.sign;
                        float_1.exponent <= float_1_in.exponent;
                        float_1.mantissa <= float_1_in.mantissa;
                    end
                    else if (float_0_req_in) begin
                        busy <= FALSE;                      
                        float_0.sign <= float_0_in.sign;
                        float_0.exponent <= float_0_in.exponent;
                        float_0.mantissa <= float_0_in.mantissa;
                        float_1 <= '0;
                    end
                    else if (float_1_req_in) begin
                        busy <= FALSE;
                        float_0 <= '0;
                        float_1.sign <= float_1_in.sign;
                        float_1.exponent <= float_1_in.exponent;
                        float_1.mantissa <= float_1_in.mantissa;
                    end
                    else begin
                        busy <= FALSE;
                        float_0 <= float_0;
                        float_1 <= float_1;
                    end
                    accum <= accum;
                    product <= '0;
                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                LOAD: begin
                    count <= count;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    // float_1 gets priority now
                    if (float_1_req_in) begin
                        busy <= TRUE;
                        float_0 <= float_0;
                        float_1.sign <= float_1_in.sign;
                        float_1.exponent <= float_1_in.exponent;
                        float_1.mantissa <= float_1_in.mantissa;
                    end                    
                    else if (float_0_req_in) begin
                        busy <= TRUE;
                        float_0.sign <= float_0_in.sign;
                        float_0.exponent <= float_0_in.exponent;
                        float_0.mantissa <= float_0_in.mantissa;
                        float_1 <= float_1;
                    end
                    else begin
                        busy <= FALSE;
                        float_0 <= float_0;
                        float_1 <= float_1;
                    end
                    accum <= accum;
                    product <= '0;
                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                MULTIPLY: begin
                    count <= count;
                    busy <= TRUE;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    float_0 <= float_0;
                    float_1 <= float_1;
                    accum <= accum;
                    product.sign <= float_0.sign ^ float_1.sign;
                    // Detect multiplication shortcuts
                    if ((!float_0.exponent && !float_0.mantissa) || (!float_1.exponent && !float_1.mantissa)) begin
                        product.exponent <= '0;
                        product.mantissa <= '0;
                    end
                    // Standard multiplication
	                else begin
	                    product.exponent <= ($signed(float_0.exponent)-EXP_OFFSET) + ($signed(float_1.exponent)-EXP_OFFSET) + EXP_OFFSET;
	                    product.mantissa <= (float_0.mantissa | (1<<MANBITS)) * (float_1.mantissa | (1<<MANBITS));
	                end

                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                ALIGN: begin
                    count <= count;
                    busy <= TRUE;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    float_0 <= float_0;
                    float_1 <= float_1;
                    // If the product is denormalized
                    if (product.mantissa[2*MANBITS+1]) begin
                        if (accum.exponent < (product.exponent+1)) begin
                            accum.sign <= accum.sign;
                            accum.exponent <= $signed(accum.exponent) + (($signed(product.exponent)+1)-$signed(accum.exponent));
                            accum.mantissa <= (accum.mantissa | (1<<MANBITS)) >> (($signed(product.exponent)+1)-$signed(accum.exponent));
                            product.sign <= product.sign;
                            product.exponent <= $signed(product.exponent) + 1;
                            product.mantissa <= product.mantissa >> 1;
                        end
                        else begin
                            accum <= accum;
                            product.sign <= product.sign;
                            product.exponent <= $signed(product.exponent) + ($signed(accum.exponent)-($signed(product.exponent)));
                            product.mantissa <= product.mantissa >> ($signed(accum.exponent)-$signed(product.exponent));
                        end
                    end
                    // Else the product is normalized
                    else begin
                        if (accum.exponent < product.exponent) begin
                            accum.sign <= accum.sign;
                            accum.exponent <= $signed(accum.exponent) + ($signed(product.exponent)-$signed(accum.exponent));
                            accum.mantissa <= (accum.mantissa | (1<<MANBITS)) >> ($signed(product.exponent)-$signed(accum.exponent));
                            product <= product;
                        end
                        else begin
                            accum <= accum;
                            product.sign <= product.sign;
                            product.exponent <= $signed(product.exponent) + ($signed(accum.exponent)-$signed(product.exponent));
                            product.mantissa <= product.mantissa >> ($signed(accum.exponent)-$signed(product.exponent));
                        end
                    end
                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                ACCUMULATE: begin
                    count <= count + 1;
                    busy <= TRUE;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    float_0 <= float_0;
                    float_1 <= float_1;
                    accum.sign <= product.sign;
                    accum.exponent <= accum.exponent;
                    // Check if adding both positive or both negative numbers
                    if ((!accum.exponent && !accum.mantissa) || (!product.exponent && !product.mantissa) || (accum.sign == product.sign)) begin
                        accum.mantissa <= product.mantissa + accum.mantissa;
                    end
                    // Else there is a subtraction to perform
                    else begin
                        if (product.mantissa >= accum.mantissa) begin
                            accum.mantissa <= product.mantissa - accum.mantissa;
                        end
                        else begin
                            accum.mantissa <= accum.mantissa - product.mantissa;
                        end
                    end
                    product <= product;
                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                NORMALIZE: begin
                    count <= count;
                    busy <= TRUE;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    float_0 <= float_0;
                    float_1 <= float_1;
                    // Normalize if multiplying the mantissas produced a 2 (denormalized)
                    if (accum.mantissa[2*MANBITS+1]) begin
                        accum.sign <= accum.sign;
                        accum.exponent <= $signed(accum.exponent) + 1;
                        accum.mantissa <= accum.mantissa >> 1;
                    end
                    else begin
                        accum <= accum;
                    end
                    product <= product;
                    float_answer_out <= '0;
                    ready_answer_out <= FALSE;
                end
                OUTPUT: begin
                    busy <= TRUE;
                    float_0_req_out <= TRUE;
                    float_1_req_out <= TRUE;
                    float_0_out.sign <= float_0.sign;
                    float_0_out.exponent <= float_0.exponent;
                    float_0_out.mantissa <= float_0.mantissa;
                    float_1_out.sign <= float_1.sign;
                    float_1_out.exponent <= float_1.exponent;
                    float_1_out.mantissa <= float_1.mantissa;
                    float_0 <= float_0;
                    float_1 <= float_1;
                    accum <= accum;
                    product <= product;
                    // Check for overflow/underflow conditions from operation
                    if (error_generated) begin
                        count <= '0;
                        float_answer_out <= '1;
                        ready_answer_out <= FALSE;
                    end
                    if (count == N) begin
                        count <= '0;
                        float_answer_out.sign <= accum.sign;
                        float_answer_out.exponent <= accum.exponent;
                        float_answer_out.mantissa <= accum.mantissa[2*MANBITS-1:MANBITS];
                        accum <= '0;
                        ready_answer_out <= TRUE;
                    end 
                    else begin
                        count <= count;
                        float_answer_out <= '0;
                        ready_answer_out <= FALSE;
                    end
                end
                ERROR: begin
                    count <= '0;
                    busy <= FALSE;
                    float_0_req_out <= FALSE;
                    float_1_req_out <= FALSE;
                    float_0_out <= '0;
                    float_1_out <= '0;
                    float_0 <= '0;
                    float_1 <= '0;
                    accum <= '0;
                    product <= '0;
                    float_answer_out <= '1;
                    ready_answer_out <= FALSE;
                end
            endcase
        end
    end

endmodule : fpu_fma
