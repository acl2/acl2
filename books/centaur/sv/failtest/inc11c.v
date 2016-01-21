
module top (output logic [3:0] out, input logic [3:0] in);

  logic [3:0] delay;

  always @(*)
    out = #3 delay++; // oops, illegal use of increment

endmodule
