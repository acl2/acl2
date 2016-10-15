// VCS and NCVerilog both reject this.

module top ;

  genvar i;
  wire 	     x, y, z;

  and i (x, y, z);   // oops, redeclaring i

endmodule
