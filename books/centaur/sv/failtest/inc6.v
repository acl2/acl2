
module top (output topout, input topin);

  // Can't have an increment in a submodule instance
  logic [3:0] w1;
  logic [3:0] w2;

  // Heh, NCVerilog permits this even though it makes no sense.
  // Fortunately VCS rejects it, at least.

  sub mysub(w1++);

endmodule


module sub(input [3:0] in);

endmodule
