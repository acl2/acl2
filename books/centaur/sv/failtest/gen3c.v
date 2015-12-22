module top ;

  parameter version = 1;

  if (version == 1)
    wire [3:0] aa = 1;
  else
    wire [3:0] aa = 2;

  wire [3:0]   bb = aa;  // oops, aa shouldn't be in scope here

endmodule
