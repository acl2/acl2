module sub #(parameter WIDTH = 1, parameter SIZE = 1)
   (output [SIZE-1:0] o,
    input [SIZE-1:0] a,
    input [SIZE-1:0] b);
   assign o = a & b;
endmodule

module top ;

   logic [1:0] o6, a6, b6;

   sub #1,2 mysub (o6, a6, b6);  // oops, need parens around parameter args

endmodule
