module top ;

  parameter version = 1;

  genvar i;
  for(i = 0;i < 1; ++i) wire [3:0] aa = i;

  wire [3:0]   bb = aa;  // oops, aa shouldn't be in scope here

endmodule
