module top (output topout, input topin);

  wire o;
  wire i;

  not foo [0] (o, i);  // oops, array of size 0.

endmodule
