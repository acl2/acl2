
module top (output topout, input topin);

  // Can't have an increment in a submodule instance
  wire [3:0] w1;
  wire [3:0] w2;

  sub mysub(w1++);

endmodule


module sub(input [3:0] in);

endmodule
