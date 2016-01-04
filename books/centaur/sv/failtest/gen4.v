module sub ;

  genvar i;

endmodule

module top ;

  wire [3:0] bb = sub.i;  // oops, hierarchical reference to genvar

endmodule
