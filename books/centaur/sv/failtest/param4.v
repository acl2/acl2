module top (output topout, input topin);

  wire [3:0] o, a, b;

  sub #(4, 1, 5) mysub (o, a, b);   // too many parameters

endmodule

module sub (o, a, b);

  parameter size = 1;
  parameter delay = 1;

  output [size-1:0] o;
  output [size-1:0] a;
  output [size-1:0] b;

  assign #delay o = a & b;

endmodule
