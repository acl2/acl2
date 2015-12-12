module top (output topout, input topin);

  wire [1:0] o;
  wire [1:0] a;
  wire [2:0] b;

  sub mysub [0] (o, a, b); // oops, 0 size instance array

endmodule


module sub (o, a, b);

  output o;
  input a;
  input b;

  assign o = a & b;

endmodule
