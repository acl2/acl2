module top ;

  genvar i;
  wire 	 w;
  assign w = i;  // oops, assignment from genvar?

endmodule
