module top (a, a);

  // Can't have ports with the same names.
  // Some Verilog tools allow this and wire the ports together.
  // But that's crazy and this just shouldn't be allowed.

  input a;

endmodule


