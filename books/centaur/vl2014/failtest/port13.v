module top (topout, topin);

  output topout;
  input  topin;

  wire a;
  wire [2:0] b;

  sub mysub(a, b);

endmodule

module sub (a, .b({b1,{b2,b3}})) ; // oops, nested concats not allowed

  output a;
  input b1;
  input b2;
  input b3;
  assign a = b1 & b2 & b3;

endmodule
