
module top;
wire foo;
if (0)
  begin : foo  // oops, declared above
  end
else
  begin: bar
  end

endmodule
