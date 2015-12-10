module top (output topout, input topin);

  wire a;
  wire [1:0] b;

  sub mysub(.a(a)); // oops, named connections but unnamed port

endmodule

module sub (a, {b1, b2}) ;

  output a;
  input b1;
  input b2;
  assign a = b1 & b2;

endmodule
