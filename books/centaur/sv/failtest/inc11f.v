
module top (output logic [3:0] out, input logic [3:0] in);

  logic [3:0] bar;
  logic [3:0] foo;
  logic       clk;

  // SystemVerilog-2012 11.3.6
  // It shall be illegal to include an assignment operator in an event expression, in an expression within a
  // procedural continuous assignment, or in an expression that is not within a procedural statement.

  always @(*)
    assign foo = (bar = in); // oops, can't use in procedural continuous assignments

endmodule
