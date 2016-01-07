module top ;

  for(i = 0;i < 1; ++i)     // oops, no genvar declaration for i
  begin : foo
    wire [3:0] aa = i;
  end

endmodule
