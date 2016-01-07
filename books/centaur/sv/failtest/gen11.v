// VCS appears to improperly permit this, but NCV rejects it

module top ;

  wire o, a, b;

  // SystemVerilog-2012 27.2 Overview: "Parameters declared in generate blocks
  // shall be treated as localparams."  So we shouldn't be allowed to override
  // the parameter.

  sub #(.whatever(3)) mysub (o, a, b);  // oops, whatever should be local

endmodule


module sub (o, a, b);

  output o;
  input  a;
  input  b;
  assign o = a & b;

  begin
    parameter whatever = 4;
  end

endmodule
