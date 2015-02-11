module top (output topout, input topin);

  wire a;
  wire [1:0] b;

  sub mysub(.a(a), .b1(b1), .b2(b2)); // oops, not using external names

endmodule

module sub (a, .b({b1, b2})) ;

  output a;
  input b1;
  input b2;
  assign a = b1 & b2;

endmodule
