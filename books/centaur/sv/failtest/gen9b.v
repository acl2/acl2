module top ;

  for(integer i = 0;i < 1; ++i)  // oops, datatype not a genvar
  begin : foo
    wire [3:0] aa = i;
  end

endmodule
