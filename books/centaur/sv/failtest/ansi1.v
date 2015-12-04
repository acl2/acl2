module top (output topout, input topin);

  wire o;
  wire a;

  sub mysub (o, a);

endmodule

module sub (o, input a) ;  // illegal mixing of ansi and non-ansi ports

  buf(o, a);

endmodule
