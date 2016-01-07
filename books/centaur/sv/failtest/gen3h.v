module top ;

  parameter version = 1;

  genvar i;
  for(i = 0;i < 1; ++i)
  begin : foo
    wire [3:0] aa = i;
  end

  wire [3:0] bb = $bits(foo.aa);  // oops, should be, e.g., foo[0].aa

endmodule
