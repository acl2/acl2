module top (output topout, input topin);

  wire [1:0] o;
  wire [1:0] a;
  wire [2:0] b;

  sub mysub [1:0] (o, a, b); // oops, can't use B because it's 3 bits instead of 2, 4, etc.

endmodule


module sub (o, a, b);

  output o;
  input a;
  input b;

  assign o = a & b;

endmodule
