module top (output topout, input topin);

  // Can't redeclare W as a wire.
  wire w = 1;
  wire w = 0;

endmodule
