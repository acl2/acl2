module top (output topout, input topin);

  // Can't have an increment in a continuous assignment
  wire [3:0] w1;
  wire [3:0] w2;

  assign w1 = w2--;

endmodule
