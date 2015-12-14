// VCS and NCVerilog both reject this.

module top ;

  wire 	     x, y, z;
  and i (x, y, z);
  genvar     i;       // oops, redeclaring i

endmodule
