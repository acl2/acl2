//@VL VL_REGRESSION_SUPPORT
module two_bit_and(o, a, b);
 output[1:0] o;
 input [1:0] a, b;
 assign o = a & b;
endmodule
