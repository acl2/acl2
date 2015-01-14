
module top (output topout, input topin);

  logic [3:0] w1;
  logic [3:0] w2;

  // This one is very tricky.
  //
  // SystemVerilog-2012 table 11-2 (page 221) gives a precedence table.
  //
  // The precedence table lists all of the unary operators at the same level,
  // i.e., we're told that + and ++ have the same precedence.
  //
  // But we don't know anything about the associativity of unary operators.
  // If all we had were prefix operators, this would make sense and most of
  // the time there would be nothing to worry about.
  //
  // However, with postincrement/decrement operators, things get trickier.
  // For instance, how is +w2++ to be parsed?  There are two reasonable
  // interpretations:
  //
  //      (+w2)++   -- illegal     This is what VCS says.
  //      +(w2++)   -- legal       This is what NCVerilog says.
  //
  // Since this is ambiguous, the safest thing seems to be to go with the VCS
  // behavior and call this a failtest.

  logic       clk;

  always @(posedge clk)
  begin
    w1 = + w2++;
  end


endmodule

