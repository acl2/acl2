module top (o, a, b);

  output o;
  input  a;

  // SystemVerilog-2012 27.2 Overview: "A generate block may not contain port
  // declarations, specify blocks, or specparam declarations."

  begin
    input  b;    // oops, generate blocks can't contain port declarations
  end

endmodule
