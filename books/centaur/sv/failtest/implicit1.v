module top (output topout, input topin);

  buf (o, i);

  // can't declare o after previously implicitly declaring it
  wire o;

endmodule
