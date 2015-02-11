module top (output topout, input topin);

  wire o, a, b;

  sub mysub (o, a, b);

endmodule


module sub (o, a, b);

  inout var o;  //  illegal to use inout and var together
  input a;
  input b;

  assign o = a & b;

endmodule
