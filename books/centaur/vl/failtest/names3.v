module top (output topout, input topin);

  wire w = 1;
  wire a, b;

  sub w(a, b);  // can't name a module instance the same as a wire

endmodule


module sub (a, b);

  input a, b;

endmodule
