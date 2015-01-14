module top (output topout, input topin);

  wire w = 1;
  wire a, b;

  buf w(a, b);  // can't name a gate w when a wire's already named that.

endmodule
