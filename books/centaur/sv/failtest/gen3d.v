module top ;

  parameter version = 1;

  genvar i;
  for(i = 0;i < 1; ++i)
  begin
    wire [3:0] aa = i;
  end

  wire [3:0]   bb = aa;  // oops, aa shouldn't be in scope here

endmodule
