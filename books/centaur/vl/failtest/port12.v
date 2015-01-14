module top (output topout, input topin);

  wire a;
  wire [1:0] b;
  wire       c;

  sub mysub(a); // oops, too few connections

endmodule

module sub (a, .b({b1, b2})) ;

  output a;
  input b1;
  input b2;
  assign a = b1 & b2;

endmodule
