
module top (output logic [3:0] out, input logic [3:0] in);

  logic [3:0] delay;
  logic       clk;

  always @(*)
    out = @(posedge clk) delay++; // oops, illegal use of increment

endmodule
