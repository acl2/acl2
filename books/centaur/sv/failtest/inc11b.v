
module top (output logic [3:0] out, input logic [3:0] in);

  logic [3:0] delay;

  always @(*)
    out = #(delay++) in; // oops, illegal use of increment and also makes no sense at all

endmodule

